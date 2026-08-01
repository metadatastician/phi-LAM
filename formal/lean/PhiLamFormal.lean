-- SPDX-License-Identifier: MPL-2.0

namespace PhiLam

structure RequestId where
  value : Nat
  deriving DecidableEq, Repr

inductive ReplayPolicy where
  | atMostOnce
  | repeatable
  deriving DecidableEq, Repr

inductive Action where
  | readMemory
  | scheduleEvaluation (requestId : RequestId) (policy : ReplayPolicy)
  | callSandbox
  deriving DecidableEq, Repr

def once (requestId : RequestId) : Action :=
  .scheduleEvaluation requestId .atMostOnce

def redundant : Action → Action → Bool
  | .scheduleEvaluation first .atMostOnce,
      .scheduleEvaluation second .atMostOnce => first == second
  | _, _ => false

@[simp] theorem redundant_once_self (requestId : RequestId) :
    redundant (once requestId) (once requestId) = true := by
  simp [once, redundant]

def normalizeTail (first : Action) : List Action → List Action
  | [] => []
  | second :: rest =>
      if redundant first second
        then normalizeTail first rest
        else second :: normalizeTail second rest

def normalize : List Action → List Action
  | [] => []
  | first :: rest => first :: normalizeTail first rest

structure StreamState where
  emitted : List Action
  pending : Option Action
  deriving DecidableEq, Repr

def emptyStream : StreamState := ⟨[], none⟩

def streamStep : StreamState → Action → StreamState
  | ⟨emitted, none⟩, action => ⟨emitted, some action⟩
  | state@⟨emitted, some previous⟩, action =>
      if redundant previous action
        then state
        else ⟨emitted ++ [previous], some action⟩

def streamChunk : StreamState → List Action → StreamState
  | state, [] => state
  | state, action :: rest => streamChunk (streamStep state action) rest

def finishStream : StreamState → List Action
  | ⟨emitted, none⟩ => emitted
  | ⟨emitted, some pending⟩ => emitted ++ [pending]

def streamNormalize (actions : List Action) : List Action :=
  finishStream (streamChunk emptyStream actions)

theorem streamChunk_append (state : StreamState)
    (left right : List Action) :
    streamChunk state (left ++ right) =
    streamChunk (streamChunk state left) right := by
  induction left generalizing state with
  | nil => rfl
  | cons action rest inductionHypothesis =>
      simp only [List.cons_append, streamChunk]
      exact inductionHypothesis (streamStep state action)

theorem finishStream_pending (emitted : List Action) (previous : Action)
    (rest : List Action) :
    finishStream (streamChunk ⟨emitted, some previous⟩ rest) =
    emitted ++ previous :: normalizeTail previous rest := by
  induction rest generalizing emitted previous with
  | nil => simp [streamChunk, finishStream, normalizeTail]
  | cons action rest inductionHypothesis =>
      by_cases pair : redundant previous action = true
      · simp [streamChunk, streamStep, pair, normalizeTail,
          inductionHypothesis emitted previous]
      · have pairFalse : redundant previous action = false := by
          cases value : redundant previous action <;> simp_all
        simp [streamChunk, streamStep, pairFalse, normalizeTail,
          inductionHypothesis (emitted ++ [previous]) action,
          List.append_assoc]

theorem finishStream_none (emitted : List Action) (actions : List Action) :
    finishStream (streamChunk ⟨emitted, none⟩ actions) =
    emitted ++ normalize actions := by
  cases actions with
  | nil => simp [streamChunk, finishStream, normalize]
  | cons first rest =>
      simpa [streamChunk, streamStep, normalize] using
        finishStream_pending emitted first rest

theorem streamNormalize_eq_normalize (actions : List Action) :
    streamNormalize actions = normalize actions := by
  simpa [streamNormalize, emptyStream] using finishStream_none [] actions

theorem streamNormalize_chunked (left right : List Action) :
    streamNormalize (left ++ right) =
    finishStream (streamChunk (streamChunk emptyStream left) right) := by
  simp [streamNormalize, streamChunk_append]

def isNormal : List Action → Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      !redundant first second && isNormal (second :: rest)

inductive Normal : List Action → Prop where
  | nil : Normal []
  | one (action : Action) : Normal [action]
  | cons (notRedundant : redundant first second = false)
      (later : Normal (second :: rest)) :
      Normal (first :: second :: rest)

theorem normalizeTail_normal (first : Action) (rest : List Action) :
    Normal (first :: normalizeTail first rest) := by
  induction rest generalizing first with
  | nil => exact .one first
  | cons second rest inductionHypothesis =>
      by_cases pair : redundant first second = true
      · simp [normalizeTail, pair]
        exact inductionHypothesis first
      · have pairFalse : redundant first second = false := by
          cases value : redundant first second <;> simp_all
        simp [normalizeTail, pairFalse]
        exact .cons pairFalse (inductionHypothesis second)

theorem normalize_normal (actions : List Action) :
    Normal (normalize actions) := by
  cases actions with
  | nil => exact .nil
  | cons first rest => exact normalizeTail_normal first rest

theorem normal_fixed {actions : List Action} (normal : Normal actions) :
    normalize actions = actions := by
  induction normal with
  | nil => rfl
  | one action => rfl
  | @cons first second rest notRedundant later inductionHypothesis =>
      simp only [normalize, normalizeTail, notRedundant, Bool.false_eq_true,
        ↓reduceIte, List.cons.injEq, true_and]
      simpa [normalize] using congrArg List.tail inductionHypothesis

theorem normalize_idempotent (actions : List Action) :
    normalize (normalize actions) = normalize actions :=
  normal_fixed (normalize_normal actions)

theorem normal_isNormal {actions : List Action} (normal : Normal actions) :
    isNormal actions = true := by
  induction normal with
  | nil => rfl
  | one action => rfl
  | cons notRedundant later inductionHypothesis =>
      simp [isNormal, notRedundant, inductionHypothesis]

theorem isNormal_normal (actions : List Action)
    (normal : isNormal actions = true) : Normal actions := by
  induction actions with
  | nil => exact .nil
  | cons first rest inductionHypothesis =>
      cases rest with
      | nil => exact .one first
      | cons second rest =>
          simp only [isNormal, Bool.and_eq_true] at normal
          have pairFalse : redundant first second = false := by
            cases value : redundant first second <;> simp_all
          exact .cons pairFalse (inductionHypothesis normal.2)

theorem normal_iff_isNormal (actions : List Action) :
    Normal actions ↔ isNormal actions = true :=
  ⟨normal_isNormal, isNormal_normal actions⟩

inductive Step : List Action → List Action → Prop where
  | prune (leading suffix : List Action) (requestId : RequestId) :
      Step
        (leading ++ once requestId :: once requestId :: suffix)
        (leading ++ once requestId :: suffix)

inductive Steps : List Action → List Action → Type where
  | refl : Steps actions actions
  | more (first : Step before middle) (later : Steps middle after) :
      Steps before after

theorem Step.prepend (action : Action) (step : Step before after) :
    Step (action :: before) (action :: after) := by
  cases step with
  | prune leading suffix requestId =>
      simpa only [List.cons_append] using
        Step.prune (action :: leading) suffix requestId

noncomputable def Steps.prepend (action : Action)
    (steps : Steps before after) :
    Steps (action :: before) (action :: after) := by
  induction steps with
  | refl => exact .refl
  | more first later inductionHypothesis =>
      exact .more (first.prepend action) inductionHypothesis

def Steps.count : Steps before after → Nat
  | .refl => 0
  | .more _ later => later.count + 1

theorem step_length_accounting (step : Step before after) :
    before.length = after.length + 1 := by
  cases step with
  | prune leading suffix requestId =>
      simp [List.length_append, Nat.add_assoc]

theorem step_decreases_length (step : Step before after) :
    after.length < before.length := by
  rw [step_length_accounting step]
  exact Nat.lt_succ_self after.length

theorem no_infinite_steps (chain : Nat → List Action)
    (next : ∀ index, Step (chain index) (chain (index + 1))) : False := by
  have accounting : ∀ index,
      (chain index).length + index = (chain 0).length := by
    intro index
    induction index with
    | zero => simp
    | succ index inductionHypothesis =>
        have decrease := step_length_accounting (next index)
        rw [← inductionHypothesis, decrease]
        simp [Nat.add_assoc, Nat.add_comm]
  let limit := (chain 0).length
  have impossible : limit + 1 ≤ limit := by
    calc
      limit + 1 ≤ (chain (limit + 1)).length + (limit + 1) :=
        Nat.le_add_left (limit + 1) (chain (limit + 1)).length
      _ = limit := accounting (limit + 1)
  exact (Nat.not_succ_le_self limit) impossible

theorem steps_length_accounting (steps : Steps before after) :
    before.length = after.length + steps.count := by
  induction steps with
  | refl => simp [Steps.count]
  | more first later inductionHypothesis =>
      rw [step_length_accounting first, inductionHypothesis]
      simp [Steps.count, Nat.add_comm, Nat.add_left_comm]

theorem steps_do_not_increase_length (steps : Steps before after) :
    after.length ≤ before.length := by
  rw [steps_length_accounting steps]
  exact Nat.le_add_right after.length steps.count

theorem normalizeTail_prune (previous : Action) (leading suffix : List Action)
    (requestId : RequestId) :
    normalizeTail previous
      (leading ++ once requestId :: once requestId :: suffix) =
    normalizeTail previous
      (leading ++ once requestId :: suffix) := by
  induction leading generalizing previous with
  | nil =>
      by_cases boundary : redundant previous (once requestId) = true
      · simp [normalizeTail, boundary]
      · have boundaryFalse : redundant previous (once requestId) = false := by
          cases value : redundant previous (once requestId) <;> simp_all
        simp [normalizeTail, boundaryFalse]
  | cons action leading inductionHypothesis =>
      by_cases boundary : redundant previous action = true
      · simp [normalizeTail, boundary, inductionHypothesis previous]
      · have boundaryFalse : redundant previous action = false := by
          cases value : redundant previous action <;> simp_all
        simp [normalizeTail, boundaryFalse, inductionHypothesis action]

theorem step_preserves_normalize (step : Step before after) :
    normalize before = normalize after := by
  cases step with
  | prune leading suffix requestId =>
      cases leading with
      | nil => simp [normalize, normalizeTail]
      | cons first leading =>
          simp only [List.cons_append, normalize, List.cons.injEq]
          exact ⟨True.intro, normalizeTail_prune first leading suffix requestId⟩

theorem steps_preserve_normalize (steps : Steps before after) :
    normalize before = normalize after := by
  induction steps with
  | refl => rfl
  | more first later inductionHypothesis =>
      exact (step_preserves_normalize first).trans inductionHypothesis

noncomputable def normalizeTail_steps (first : Action) (rest : List Action) :
    Steps (first :: rest) (first :: normalizeTail first rest) := by
  induction rest generalizing first with
  | nil => exact .refl
  | cons second rest inductionHypothesis =>
      by_cases pair : redundant first second = true
      · cases first <;> cases second <;> simp [redundant] at pair
        case scheduleEvaluation.scheduleEvaluation firstId firstPolicy secondId secondPolicy =>
          cases firstPolicy <;> cases secondPolicy <;> simp at pair
          subst secondId
          have selfRedundant :
              redundant
                (.scheduleEvaluation firstId .atMostOnce)
                (.scheduleEvaluation firstId .atMostOnce) = true := by
            simp [redundant]
          simpa only [normalizeTail, selfRedundant, if_pos, once,
            List.nil_append] using
            Steps.more (Step.prune [] rest firstId)
              (inductionHypothesis (once firstId))
      · have pairFalse : redundant first second = false := by
          cases value : redundant first second <;> simp_all
        simpa [normalizeTail, pairFalse] using
          (inductionHypothesis second).prepend first

noncomputable def normalize_steps (actions : List Action) :
    Steps actions (normalize actions) := by
  cases actions with
  | nil => exact .refl
  | cons first rest => exact normalizeTail_steps first rest

theorem reachable_normal_eq_normalize (steps : Steps input candidate)
    (normal : Normal candidate) : candidate = normalize input := by
  have invariant := steps_preserve_normalize steps
  rw [normal_fixed normal] at invariant
  exact invariant.symm

def Joinable (left right : List Action) : Type :=
  Σ common : List Action, Steps left common × Steps right common

noncomputable def steps_confluent (leftSteps : Steps input left)
    (rightSteps : Steps input right) : Joinable left right := by
  have leftInvariant := steps_preserve_normalize leftSteps
  have rightInvariant := steps_preserve_normalize rightSteps
  refine ⟨normalize input, ?_, ?_⟩
  · rw [leftInvariant]
    exact normalize_steps left
  · rw [rightInvariant]
    exact normalize_steps right

theorem reachable_normal_unique (leftSteps : Steps input left)
    (rightSteps : Steps input right) (leftNormal : Normal left)
    (rightNormal : Normal right) : left = right := by
  rw [reachable_normal_eq_normalize leftSteps leftNormal]
  exact (reachable_normal_eq_normalize rightSteps rightNormal).symm

structure SchedulerModel (State : Type) where
  readMemory : State → State
  scheduleEvaluation : RequestId → ReplayPolicy → State → State
  callSandbox : State → State
  atMostOnceIdempotent : ∀ requestId initial,
    scheduleEvaluation requestId .atMostOnce
      (scheduleEvaluation requestId .atMostOnce initial) =
    scheduleEvaluation requestId .atMostOnce initial

def applyAction (model : SchedulerModel State) : Action → State → State
  | .readMemory => model.readMemory
  | .scheduleEvaluation requestId policy =>
      model.scheduleEvaluation requestId policy
  | .callSandbox => model.callSandbox

def interpret (model : SchedulerModel State) : List Action → State → State
  | [], initial => initial
  | action :: rest, initial =>
      interpret model rest (applyAction model action initial)

theorem interpret_append (model : SchedulerModel State)
    (leading suffix : List Action) (initial : State) :
    interpret model (leading ++ suffix) initial =
    interpret model suffix (interpret model leading initial) := by
  induction leading generalizing initial with
  | nil => rfl
  | cons action rest inductionHypothesis =>
      simp only [List.cons_append, interpret]
      exact inductionHypothesis (applyAction model action initial)

theorem step_preserves_semantics (model : SchedulerModel State)
    (step : Step before after) (initial : State) :
    interpret model before initial = interpret model after initial := by
  cases step with
  | prune leading suffix requestId =>
      simp only [interpret_append, interpret, once, applyAction]
      rw [model.atMostOnceIdempotent]

theorem steps_preserve_semantics (model : SchedulerModel State)
    (steps : Steps before after) (initial : State) :
    interpret model before initial = interpret model after initial := by
  induction steps generalizing initial with
  | refl => rfl
  | more first later inductionHypothesis =>
      exact (step_preserves_semantics model first initial).trans
        (inductionHypothesis initial)

theorem normalize_preserves_semantics (model : SchedulerModel State)
    (actions : List Action) (initial : State) :
    interpret model actions initial =
    interpret model (normalize actions) initial :=
  steps_preserve_semantics model (normalize_steps actions) initial

end PhiLam
