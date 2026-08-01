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

inductive Step : List Action → List Action → Prop where
  | prune (leading suffix : List Action) (requestId : RequestId) :
      Step
        (leading ++ once requestId :: once requestId :: suffix)
        (leading ++ once requestId :: suffix)

inductive Steps : List Action → List Action → Prop where
  | refl : Steps actions actions
  | more (first : Step before middle) (later : Steps middle after) :
      Steps before after

theorem Step.prepend (action : Action) (step : Step before after) :
    Step (action :: before) (action :: after) := by
  cases step with
  | prune leading suffix requestId =>
      simpa only [List.cons_append] using
        Step.prune (action :: leading) suffix requestId

theorem Steps.prepend (action : Action) (steps : Steps before after) :
    Steps (action :: before) (action :: after) := by
  induction steps with
  | refl => exact .refl
  | more first later inductionHypothesis =>
      exact .more (first.prepend action) inductionHypothesis

theorem normalizeTail_steps (first : Action) (rest : List Action) :
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

theorem normalize_steps (actions : List Action) :
    Steps actions (normalize actions) := by
  cases actions with
  | nil => exact .refl
  | cons first rest => exact normalizeTail_steps first rest

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
