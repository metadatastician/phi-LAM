-- SPDX-License-Identifier: MPL-2.0

module PhiLam.ReferenceScheduler

import PhiLam.Action
import PhiLam.Normalize
import PhiLam.Semantics

%default total

sameNat : Nat -> Nat -> Bool
sameNat Z Z = True
sameNat Z (S _) = False
sameNat (S _) Z = False
sameNat (S left) (S right) = sameNat left right

sameNatRefl : (value : Nat) -> sameNat value value = True
sameNatRefl Z = Refl
sameNatRefl (S value) = sameNatRefl value

sameRequest : RequestId -> RequestId -> Bool
sameRequest (MkRequestId left) (MkRequestId right) = sameNat left right

sameRequestRefl : (requestId : RequestId) ->
                  sameRequest requestId requestId = True
sameRequestRefl (MkRequestId value) = sameNatRefl value

||| Executable membership predicate for the reference scheduler's seen set.
public export
containsRequest : RequestId -> List RequestId -> Bool
containsRequest _ [] = False
containsRequest requestId (candidate :: rest) =
  if sameRequest requestId candidate
    then True
    else containsRequest requestId rest

containsInserted : (requestId : RequestId) -> (seen : List RequestId) ->
                   containsRequest requestId (requestId :: seen) = True
containsInserted requestId seen =
  rewrite sameRequestRefl requestId in Refl

||| No request identity occurs more than once in the scheduler's seen set.
public export
data UniqueRequests : List RequestId -> Type where
  UniqueNil : UniqueRequests []
  UniqueCons : containsRequest requestId rest = False ->
               UniqueRequests rest ->
               UniqueRequests (requestId :: rest)

||| An externally effective scheduling request.
public export
record ScheduledRequest where
  constructor MkScheduledRequest
  requestId : RequestId
  replayPolicy : ReplayPolicy

public export
Eq ScheduledRequest where
  left == right =
    requestId left == requestId right &&
    replayPolicy left == replayPolicy right

public export
Show ScheduledRequest where
  show request =
    "Scheduled(" ++ show (requestId request) ++ ", " ++
    show (replayPolicy request) ++ ")"

||| Effective state: diagnostics are deliberately not part of this record.
public export
record SchedulerState where
  constructor MkSchedulerState
  seenAtMostOnce : List RequestId
  effectiveSchedule : List ScheduledRequest
  memoryReads : Nat
  sandboxCalls : Nat

public export
Eq SchedulerState where
  left == right =
    seenAtMostOnce left == seenAtMostOnce right &&
    effectiveSchedule left == effectiveSchedule right &&
    memoryReads left == memoryReads right &&
    sandboxCalls left == sandboxCalls right

public export
Show SchedulerState where
  show state =
    "SchedulerState(seen=" ++ show (seenAtMostOnce state) ++
    ", effective=" ++ show (effectiveSchedule state) ++
    ", reads=" ++ show (memoryReads state) ++
    ", sandboxes=" ++ show (sandboxCalls state) ++ ")"

||| Accepted at-most-once identities, in effective acceptance order.
public export
atMostOnceIds : List ScheduledRequest -> List RequestId
atMostOnceIds [] = []
atMostOnceIds (MkScheduledRequest requestId AtMostOnce :: rest) =
  requestId :: atMostOnceIds rest
atMostOnceIds (MkScheduledRequest _ Repeatable :: rest) =
  atMostOnceIds rest

atMostOnceIdsAppendOnce :
  (requests : List ScheduledRequest) -> (requestId : RequestId) ->
  atMostOnceIds
    (requests ++ [MkScheduledRequest requestId AtMostOnce]) =
  atMostOnceIds requests ++ [requestId]
atMostOnceIdsAppendOnce [] requestId = Refl
atMostOnceIdsAppendOnce
  (MkScheduledRequest acceptedId AtMostOnce :: rest) requestId =
    cong (acceptedId ::) (atMostOnceIdsAppendOnce rest requestId)
atMostOnceIdsAppendOnce
  (MkScheduledRequest acceptedId Repeatable :: rest) requestId =
    atMostOnceIdsAppendOnce rest requestId

atMostOnceIdsAppendRepeatable :
  (requests : List ScheduledRequest) -> (requestId : RequestId) ->
  atMostOnceIds
    (requests ++ [MkScheduledRequest requestId Repeatable]) =
  atMostOnceIds requests
atMostOnceIdsAppendRepeatable [] requestId = Refl
atMostOnceIdsAppendRepeatable
  (MkScheduledRequest acceptedId AtMostOnce :: rest) requestId =
    cong (acceptedId ::) (atMostOnceIdsAppendRepeatable rest requestId)
atMostOnceIdsAppendRepeatable
  (MkScheduledRequest acceptedId Repeatable :: rest) requestId =
    atMostOnceIdsAppendRepeatable rest requestId

appendAssoc : (left : List element) -> (middle : List element) ->
              (right : List element) ->
  (left ++ middle) ++ right = left ++ (middle ++ right)
appendAssoc [] middle right = Refl
appendAssoc (item :: rest) middle right =
  cong (item ::) (appendAssoc rest middle right)

reverseOntoAppend :
  (accumulator : List element) -> (items : List element) ->
  reverseOnto accumulator items =
  reverseOnto [] items ++ accumulator
reverseOntoAppend accumulator [] = Refl
reverseOntoAppend accumulator (item :: rest) =
  rewrite reverseOntoAppend (item :: accumulator) rest in
  rewrite reverseOntoAppend [item] rest in
  rewrite appendAssoc (reverseOnto [] rest) [item] accumulator in Refl

reversePrepend : (item : element) -> (rest : List element) ->
  reverse (item :: rest) = reverse rest ++ [item]
reversePrepend item rest = reverseOntoAppend [item] rest

||| A coherent reachable scheduler state.
|||
||| Seen identities are unique and, when reversed into acceptance order,
||| exactly match the at-most-once entries in the effective schedule.
public export
record WellFormed (state : SchedulerState) where
  constructor MkWellFormed
  uniqueSeen : UniqueRequests (seenAtMostOnce state)
  acceptedOrder :
    reverse (seenAtMostOnce state) =
    atMostOnceIds (effectiveSchedule state)

uniqueRequestsCheck : List RequestId -> Bool
uniqueRequestsCheck [] = True
uniqueRequestsCheck (requestId :: rest) =
  not (containsRequest requestId rest) && uniqueRequestsCheck rest

||| Executable coherence predicate for tests and untyped boundaries.
public export
isWellFormed : SchedulerState -> Bool
isWellFormed state =
  uniqueRequestsCheck (seenAtMostOnce state) &&
  reverse (seenAtMostOnce state) == atMostOnceIds (effectiveSchedule state)

||| The empty effective scheduler state.
public export
emptyState : SchedulerState
emptyState = MkSchedulerState [] [] 0 0

||| The initial scheduler state is coherent.
public export
emptyWellFormed : WellFormed PhiLam.ReferenceScheduler.emptyState
emptyWellFormed = MkWellFormed UniqueNil Refl

||| Schedule an evaluation according to its replay policy.
public export
schedule : RequestId -> ReplayPolicy -> SchedulerState -> SchedulerState
schedule requestId AtMostOnce state =
  if containsRequest requestId (seenAtMostOnce state)
    then state
    else MkSchedulerState
      (requestId :: seenAtMostOnce state)
      (effectiveSchedule state ++
        [MkScheduledRequest requestId AtMostOnce])
      (memoryReads state)
      (sandboxCalls state)
schedule requestId Repeatable state =
  MkSchedulerState
    (seenAtMostOnce state)
    (effectiveSchedule state ++
      [MkScheduledRequest requestId Repeatable])
    (memoryReads state)
    (sandboxCalls state)

scheduleWhenSeen :
  (requestId : RequestId) ->
  (seen : List RequestId) ->
  (effective : List ScheduledRequest) ->
  (reads : Nat) -> (sandboxes : Nat) ->
  containsRequest requestId seen = True ->
  schedule requestId AtMostOnce
    (MkSchedulerState seen effective reads sandboxes) =
  MkSchedulerState seen effective reads sandboxes
scheduleWhenSeen requestId seen effective reads sandboxes alreadySeen =
  rewrite alreadySeen in Refl

scheduleWhenUnseen :
  (requestId : RequestId) ->
  (seen : List RequestId) ->
  (effective : List ScheduledRequest) ->
  (reads : Nat) -> (sandboxes : Nat) ->
  containsRequest requestId seen = False ->
  schedule requestId AtMostOnce
    (MkSchedulerState seen effective reads sandboxes) =
  MkSchedulerState
    (requestId :: seen)
    (effective ++ [MkScheduledRequest requestId AtMostOnce])
    reads sandboxes
scheduleWhenUnseen requestId seen effective reads sandboxes notSeen =
  rewrite notSeen in Refl

scheduleRepeatable :
  (requestId : RequestId) ->
  (seen : List RequestId) ->
  (effective : List ScheduledRequest) ->
  (reads : Nat) -> (sandboxes : Nat) ->
  schedule requestId Repeatable
    (MkSchedulerState seen effective reads sandboxes) =
  MkSchedulerState
    seen
    (effective ++ [MkScheduledRequest requestId Repeatable])
    reads sandboxes
scheduleRepeatable requestId seen effective reads sandboxes = Refl

containsAfterAtMostOnceScheduleByDecision :
  (requestId : RequestId) ->
  (seen : List RequestId) ->
  (effective : List ScheduledRequest) ->
  (reads : Nat) -> (sandboxes : Nat) ->
  (decision : Bool) ->
  containsRequest requestId seen = decision ->
  containsRequest requestId
    (seenAtMostOnce
      (schedule requestId AtMostOnce
        (MkSchedulerState seen effective reads sandboxes))) = True
containsAfterAtMostOnceScheduleByDecision requestId seen effective
  reads sandboxes True alreadySeen =
    let transition = scheduleWhenSeen
          requestId seen effective reads sandboxes alreadySeen
     in replace
          {p = \state =>
            containsRequest requestId (seenAtMostOnce state) = True}
          (sym transition)
          alreadySeen
containsAfterAtMostOnceScheduleByDecision requestId seen effective
  reads sandboxes False notSeen =
    let transition = scheduleWhenUnseen
          requestId seen effective reads sandboxes notSeen
     in replace
          {p = \state =>
            containsRequest requestId (seenAtMostOnce state) = True}
          (sym transition)
          (containsInserted requestId seen)

||| After any at-most-once scheduling attempt, that identity is in the seen set.
public export
containsAfterAtMostOnceSchedule :
  (requestId : RequestId) -> (initial : SchedulerState) ->
  containsRequest requestId
    (seenAtMostOnce (schedule requestId AtMostOnce initial)) = True
containsAfterAtMostOnceSchedule requestId
  (MkSchedulerState seen effective reads sandboxes) =
    containsAfterAtMostOnceScheduleByDecision
      requestId seen effective reads sandboxes
      (containsRequest requestId seen) Refl

newAtMostOnceWellFormed :
  (requestId : RequestId) ->
  (seen : List RequestId) ->
  (effective : List ScheduledRequest) ->
  (reads : Nat) -> (sandboxes : Nat) ->
  WellFormed (MkSchedulerState seen effective reads sandboxes) ->
  containsRequest requestId seen = False ->
  WellFormed
    (MkSchedulerState
      (requestId :: seen)
      (effective ++ [MkScheduledRequest requestId AtMostOnce])
      reads sandboxes)
newAtMostOnceWellFormed requestId seen effective reads sandboxes
  (MkWellFormed unique order) notSeen =
    MkWellFormed
      (UniqueCons notSeen unique)
      (trans
        (reversePrepend requestId seen)
        (trans
          (cong (++ [requestId]) order)
          (sym (atMostOnceIdsAppendOnce effective requestId))))

newRepeatableWellFormed :
  (requestId : RequestId) ->
  (seen : List RequestId) ->
  (effective : List ScheduledRequest) ->
  (reads : Nat) -> (sandboxes : Nat) ->
  WellFormed (MkSchedulerState seen effective reads sandboxes) ->
  WellFormed
    (MkSchedulerState
      seen
      (effective ++ [MkScheduledRequest requestId Repeatable])
      reads sandboxes)
newRepeatableWellFormed requestId seen effective reads sandboxes
  (MkWellFormed unique order) =
    MkWellFormed unique
      (trans order (sym (atMostOnceIdsAppendRepeatable effective requestId)))

schedulePreservesWellFormedByDecision :
  (requestId : RequestId) -> (policy : ReplayPolicy) ->
  (seen : List RequestId) ->
  (effective : List ScheduledRequest) ->
  (reads : Nat) -> (sandboxes : Nat) ->
  (coherent : WellFormed
    (MkSchedulerState seen effective reads sandboxes)) ->
  (decision : Bool) ->
  containsRequest requestId seen = decision ->
  WellFormed
    (schedule requestId policy
      (MkSchedulerState seen effective reads sandboxes))
schedulePreservesWellFormedByDecision requestId AtMostOnce
  seen effective reads sandboxes coherent True alreadySeen =
    let transition = scheduleWhenSeen
          requestId seen effective reads sandboxes alreadySeen
     in replace {p = WellFormed} (sym transition) coherent
schedulePreservesWellFormedByDecision requestId AtMostOnce
  seen effective reads sandboxes coherent False notSeen =
    let transition = scheduleWhenUnseen
          requestId seen effective reads sandboxes notSeen
        nextIsWellFormed = newAtMostOnceWellFormed
          requestId seen effective reads sandboxes coherent notSeen
     in replace {p = WellFormed} (sym transition) nextIsWellFormed
schedulePreservesWellFormedByDecision requestId Repeatable
  seen effective reads sandboxes coherent decision _ =
    let transition = scheduleRepeatable
          requestId seen effective reads sandboxes
        nextIsWellFormed = newRepeatableWellFormed
          requestId seen effective reads sandboxes coherent
     in replace {p = WellFormed} (sym transition) nextIsWellFormed

||| Every scheduling transition preserves coherent state.
public export
schedulePreservesWellFormed :
  (requestId : RequestId) -> (policy : ReplayPolicy) ->
  (initial : SchedulerState) ->
  WellFormed initial -> WellFormed (schedule requestId policy initial)
schedulePreservesWellFormed requestId policy
  (MkSchedulerState seen effective reads sandboxes) coherent =
    schedulePreservesWellFormedByDecision
      requestId policy seen effective reads sandboxes coherent
      (containsRequest requestId seen) Refl

scheduleAtMostOnceIdempotentByDecision :
  (requestId : RequestId) ->
  (seen : List RequestId) ->
  (effective : List ScheduledRequest) ->
  (reads : Nat) -> (sandboxes : Nat) ->
  (decision : Bool) ->
  containsRequest requestId seen = decision ->
  schedule requestId AtMostOnce
    (schedule requestId AtMostOnce
      (MkSchedulerState seen effective reads sandboxes)) =
  schedule requestId AtMostOnce
    (MkSchedulerState seen effective reads sandboxes)
scheduleAtMostOnceIdempotentByDecision
  requestId seen effective reads sandboxes True alreadySeen =
    rewrite alreadySeen in
    rewrite alreadySeen in Refl
scheduleAtMostOnceIdempotentByDecision
  requestId seen effective reads sandboxes False notSeen =
    rewrite notSeen in
    rewrite containsInserted requestId seen in Refl

||| The same at-most-once request is an idempotent state transition.
public export
scheduleAtMostOnceIdempotent :
  (requestId : RequestId) -> (initial : SchedulerState) ->
  schedule requestId AtMostOnce
    (schedule requestId AtMostOnce initial) =
  schedule requestId AtMostOnce initial
scheduleAtMostOnceIdempotent requestId
  (MkSchedulerState seen effective reads sandboxes) =
    scheduleAtMostOnceIdempotentByDecision
      requestId seen effective reads sandboxes
      (containsRequest requestId seen) Refl

readMemoryTransition : SchedulerState -> SchedulerState
readMemoryTransition state =
  MkSchedulerState
    (seenAtMostOnce state)
    (effectiveSchedule state)
    (S (memoryReads state))
    (sandboxCalls state)

callSandboxTransition : SchedulerState -> SchedulerState
callSandboxTransition state =
  MkSchedulerState
    (seenAtMostOnce state)
    (effectiveSchedule state)
    (memoryReads state)
    (S (sandboxCalls state))

||| The verified pure scheduler as an instance of the abstract model.
public export
referenceModel : SchedulerModel SchedulerState
referenceModel = MkSchedulerModel
  readMemoryTransition
  schedule
  callSandboxTransition
  scheduleAtMostOnceIdempotent

||| Every symbolic action preserves coherent reference-scheduler state.
public export
applyActionPreservesWellFormed :
  (action : Action) -> (initial : SchedulerState) ->
  WellFormed initial ->
  WellFormed
    (applyAction PhiLam.ReferenceScheduler.referenceModel action initial)
applyActionPreservesWellFormed ReadMemory
  (MkSchedulerState seen effective reads sandboxes)
  (MkWellFormed unique order) = MkWellFormed unique order
applyActionPreservesWellFormed
  (ScheduleEvaluation requestId policy) initial coherent =
    schedulePreservesWellFormed requestId policy initial coherent
applyActionPreservesWellFormed CallSandbox
  (MkSchedulerState seen effective reads sandboxes)
  (MkWellFormed unique order) = MkWellFormed unique order

||| Interpreting any finite action sequence preserves scheduler coherence.
public export
interpretPreservesWellFormed :
  (actions : List Action) -> (initial : SchedulerState) ->
  WellFormed initial ->
  WellFormed
    (interpret PhiLam.ReferenceScheduler.referenceModel actions initial)
interpretPreservesWellFormed [] initial coherent = coherent
interpretPreservesWellFormed (action :: rest) initial coherent =
  interpretPreservesWellFormed rest
    (applyAction PhiLam.ReferenceScheduler.referenceModel action initial)
    (applyActionPreservesWellFormed action initial coherent)

plusSuccRight : (left : Nat) -> (right : Nat) ->
  left + S right = S (left + right)
plusSuccRight Z right = Refl
plusSuccRight (S left) right = cong S (plusSuccRight left right)

||| Number of memory-read actions in a symbolic sequence.
public export
countMemoryReads : List Action -> Nat
countMemoryReads [] = 0
countMemoryReads (ReadMemory :: rest) = S (countMemoryReads rest)
countMemoryReads (_ :: rest) = countMemoryReads rest

||| Number of sandbox-call actions in a symbolic sequence.
public export
countSandboxCalls : List Action -> Nat
countSandboxCalls [] = 0
countSandboxCalls (CallSandbox :: rest) = S (countSandboxCalls rest)
countSandboxCalls (_ :: rest) = countSandboxCalls rest

||| Number of at-most-once scheduling attempts in a symbolic sequence.
public export
countAtMostOnceAttempts : List Action -> Nat
countAtMostOnceAttempts [] = 0
countAtMostOnceAttempts
  (ScheduleEvaluation _ AtMostOnce :: rest) =
    S (countAtMostOnceAttempts rest)
countAtMostOnceAttempts (_ :: rest) = countAtMostOnceAttempts rest

schedulePreservesCountersByDecision :
  (requestId : RequestId) -> (policy : ReplayPolicy) ->
  (seen : List RequestId) ->
  (effective : List ScheduledRequest) ->
  (reads : Nat) -> (sandboxes : Nat) ->
  (decision : Bool) ->
  containsRequest requestId seen = decision ->
  ( memoryReads
      (schedule requestId policy
        (MkSchedulerState seen effective reads sandboxes)) = reads
  , sandboxCalls
      (schedule requestId policy
        (MkSchedulerState seen effective reads sandboxes)) = sandboxes
  )
schedulePreservesCountersByDecision requestId AtMostOnce
  seen effective reads sandboxes True alreadySeen =
    rewrite alreadySeen in (Refl, Refl)
schedulePreservesCountersByDecision requestId AtMostOnce
  seen effective reads sandboxes False notSeen =
    rewrite notSeen in (Refl, Refl)
schedulePreservesCountersByDecision requestId Repeatable
  seen effective reads sandboxes decision _ = (Refl, Refl)

schedulePreservesCounters :
  (requestId : RequestId) -> (policy : ReplayPolicy) ->
  (initial : SchedulerState) ->
  ( memoryReads (schedule requestId policy initial) = memoryReads initial
  , sandboxCalls (schedule requestId policy initial) = sandboxCalls initial
  )
schedulePreservesCounters requestId policy
  (MkSchedulerState seen effective reads sandboxes) =
    schedulePreservesCountersByDecision
      requestId policy seen effective reads sandboxes
      (containsRequest requestId seen) Refl

||| Reference interpretation changes the memory counter by exactly the number
||| of memory-read actions and by nothing else.
public export
interpretMemoryReadsExactly :
  (actions : List Action) -> (initial : SchedulerState) ->
  memoryReads
    (interpret PhiLam.ReferenceScheduler.referenceModel actions initial) =
  countMemoryReads actions + memoryReads initial
interpretMemoryReadsExactly [] initial = Refl
interpretMemoryReadsExactly (ReadMemory :: rest)
  (MkSchedulerState seen effective reads sandboxes) =
    trans
      (interpretMemoryReadsExactly rest
        (MkSchedulerState seen effective (S reads) sandboxes))
      (plusSuccRight (countMemoryReads rest) reads)
interpretMemoryReadsExactly
  (ScheduleEvaluation requestId policy :: rest) initial =
    trans
      (interpretMemoryReadsExactly rest
        (schedule requestId policy initial))
      (cong (countMemoryReads rest +)
        (fst (schedulePreservesCounters requestId policy initial)))
interpretMemoryReadsExactly (CallSandbox :: rest)
  (MkSchedulerState seen effective reads sandboxes) =
    interpretMemoryReadsExactly rest
      (MkSchedulerState seen effective reads (S sandboxes))

||| Reference interpretation changes the sandbox counter by exactly the number
||| of sandbox-call actions and by nothing else.
public export
interpretSandboxCallsExactly :
  (actions : List Action) -> (initial : SchedulerState) ->
  sandboxCalls
    (interpret PhiLam.ReferenceScheduler.referenceModel actions initial) =
  countSandboxCalls actions + sandboxCalls initial
interpretSandboxCallsExactly [] initial = Refl
interpretSandboxCallsExactly (ReadMemory :: rest)
  (MkSchedulerState seen effective reads sandboxes) =
    interpretSandboxCallsExactly rest
      (MkSchedulerState seen effective (S reads) sandboxes)
interpretSandboxCallsExactly
  (ScheduleEvaluation requestId policy :: rest) initial =
    trans
      (interpretSandboxCallsExactly rest
        (schedule requestId policy initial))
      (cong (countSandboxCalls rest +)
        (snd (schedulePreservesCounters requestId policy initial)))
interpretSandboxCallsExactly (CallSandbox :: rest)
  (MkSchedulerState seen effective reads sandboxes) =
    trans
      (interpretSandboxCallsExactly rest
        (MkSchedulerState seen effective reads (S sandboxes)))
      (plusSuccRight (countSandboxCalls rest) sandboxes)

||| Concrete specialization of the model-parametric preservation theorem.
public export
referenceNormalizationPreservesSemantics :
  (actions : List Action) -> (initial : SchedulerState) ->
  interpret PhiLam.ReferenceScheduler.referenceModel actions initial =
  interpret PhiLam.ReferenceScheduler.referenceModel
    (normalized (normalize actions)) initial
referenceNormalizationPreservesSemantics actions initial =
  normalizePreservesSemantics
    PhiLam.ReferenceScheduler.referenceModel actions initial

||| Diagnostics describe suppression without changing effective semantics.
public export
data Diagnostic = SuppressedDuplicate RequestId

public export
Eq Diagnostic where
  SuppressedDuplicate left == SuppressedDuplicate right = left == right

public export
Show Diagnostic where
  show (SuppressedDuplicate requestId) =
    "SuppressedDuplicate(" ++ show requestId ++ ")"

public export
diagnosticFor : Action -> SchedulerState -> List Diagnostic
diagnosticFor (ScheduleEvaluation requestId AtMostOnce) state =
  if containsRequest requestId (seenAtMostOnce state)
    then [SuppressedDuplicate requestId]
    else []
diagnosticFor _ _ = []

||| State produced when a previously unseen at-most-once request is accepted.
public export
acceptedState : RequestId -> SchedulerState -> SchedulerState
acceptedState requestId state =
  MkSchedulerState
    (requestId :: seenAtMostOnce state)
    (effectiveSchedule state ++
      [MkScheduledRequest requestId AtMostOnce])
    (memoryReads state)
    (sandboxCalls state)

diagnosticWhenSeen :
  (requestId : RequestId) ->
  (seen : List RequestId) ->
  (effective : List ScheduledRequest) ->
  (reads : Nat) -> (sandboxes : Nat) ->
  containsRequest requestId seen = True ->
  diagnosticFor
    (ScheduleEvaluation requestId AtMostOnce)
    (MkSchedulerState seen effective reads sandboxes) =
  [SuppressedDuplicate requestId]
diagnosticWhenSeen requestId seen effective reads sandboxes alreadySeen =
  rewrite alreadySeen in Refl

diagnosticWhenUnseen :
  (requestId : RequestId) ->
  (seen : List RequestId) ->
  (effective : List ScheduledRequest) ->
  (reads : Nat) -> (sandboxes : Nat) ->
  containsRequest requestId seen = False ->
  diagnosticFor
    (ScheduleEvaluation requestId AtMostOnce)
    (MkSchedulerState seen effective reads sandboxes) = []
diagnosticWhenUnseen requestId seen effective reads sandboxes notSeen =
  rewrite notSeen in Refl

||| Re-attempting immediately after an at-most-once attempt always emits the
||| corresponding suppression diagnostic.
public export
diagnosticAfterAtMostOnceSchedule :
  (requestId : RequestId) -> (initial : SchedulerState) ->
  diagnosticFor
    (ScheduleEvaluation requestId AtMostOnce)
    (schedule requestId AtMostOnce initial) =
  [SuppressedDuplicate requestId]
diagnosticAfterAtMostOnceSchedule requestId initial =
  rewrite containsAfterAtMostOnceSchedule requestId initial in Refl

||| Complete evidence for the two possible at-most-once outcomes.
public export
data AtMostOnceDecision :
  (attemptId : RequestId) -> (initial : SchedulerState) -> Type where
  AcceptedAttempt :
    containsRequest attemptId (seenAtMostOnce initial) = False ->
    schedule attemptId AtMostOnce initial = acceptedState attemptId initial ->
    diagnosticFor (ScheduleEvaluation attemptId AtMostOnce) initial = [] ->
    AtMostOnceDecision attemptId initial
  SuppressedAttempt :
    containsRequest attemptId (seenAtMostOnce initial) = True ->
    schedule attemptId AtMostOnce initial = initial ->
    diagnosticFor (ScheduleEvaluation attemptId AtMostOnce) initial =
      [SuppressedDuplicate attemptId] ->
    AtMostOnceDecision attemptId initial

atMostOnceDecisionByMembership :
  (requestId : RequestId) ->
  (seen : List RequestId) ->
  (effective : List ScheduledRequest) ->
  (reads : Nat) -> (sandboxes : Nat) ->
  (decision : Bool) ->
  containsRequest requestId seen = decision ->
  AtMostOnceDecision requestId
    (MkSchedulerState seen effective reads sandboxes)
atMostOnceDecisionByMembership requestId seen effective reads sandboxes
  True alreadySeen =
    SuppressedAttempt
      alreadySeen
      (scheduleWhenSeen
        requestId seen effective reads sandboxes alreadySeen)
      (diagnosticWhenSeen
        requestId seen effective reads sandboxes alreadySeen)
atMostOnceDecisionByMembership requestId seen effective reads sandboxes
  False notSeen =
    AcceptedAttempt
      notSeen
      (scheduleWhenUnseen
        requestId seen effective reads sandboxes notSeen)
      (diagnosticWhenUnseen
        requestId seen effective reads sandboxes notSeen)

||| Every at-most-once attempt is constructively classified as accepted or
||| suppressed, with its effective transition and diagnostic proved together.
public export
classifyAtMostOnce :
  (requestId : RequestId) -> (initial : SchedulerState) ->
  AtMostOnceDecision requestId initial
classifyAtMostOnce requestId
  (MkSchedulerState seen effective reads sandboxes) =
    atMostOnceDecisionByMembership
      requestId seen effective reads sandboxes
      (containsRequest requestId seen) Refl

collectDiagnostics : List Action -> SchedulerState -> List Diagnostic
collectDiagnostics [] _ = []
collectDiagnostics (action :: rest) state =
  diagnosticFor action state ++
  collectDiagnostics rest (applyAction referenceModel action state)

lengthWithInserted :
  (leading : List element) -> (item : element) ->
  (suffix : List element) ->
  length (leading ++ item :: suffix) =
  S (length (leading ++ suffix))
lengthWithInserted [] item suffix = Refl
lengthWithInserted (value :: rest) item suffix =
  cong S (lengthWithInserted rest item suffix)

lengthPrefixPreservesSuccessor :
  (leading : List element) ->
  length before = S (length after) ->
  length (leading ++ before) = S (length (leading ++ after))
lengthPrefixPreservesSuccessor [] difference = difference
lengthPrefixPreservesSuccessor (value :: rest) difference =
  cong S (lengthPrefixPreservesSuccessor rest difference)

duplicateAddsSuppression :
  (requestId : RequestId) -> (suffix : List Action) ->
  (initial : SchedulerState) ->
  length
    (collectDiagnostics
      (ScheduleEvaluation requestId AtMostOnce ::
       ScheduleEvaluation requestId AtMostOnce :: suffix)
      initial) =
  S (length
    (collectDiagnostics
      (ScheduleEvaluation requestId AtMostOnce :: suffix)
      initial))
duplicateAddsSuppression requestId suffix initial =
  rewrite diagnosticAfterAtMostOnceSchedule requestId initial in
  rewrite scheduleAtMostOnceIdempotent requestId initial in
  lengthWithInserted
    (diagnosticFor (ScheduleEvaluation requestId AtMostOnce) initial)
    (SuppressedDuplicate requestId)
    (collectDiagnostics suffix (schedule requestId AtMostOnce initial))

pruneAddsSuppression :
  (leading : List Action) -> (suffix : List Action) ->
  (requestId : RequestId) -> (initial : SchedulerState) ->
  length
    (collectDiagnostics
      (leading ++
       ScheduleEvaluation requestId AtMostOnce ::
       ScheduleEvaluation requestId AtMostOnce :: suffix)
      initial) =
  S (length
    (collectDiagnostics
      (leading ++ ScheduleEvaluation requestId AtMostOnce :: suffix)
      initial))
pruneAddsSuppression [] suffix requestId initial =
  duplicateAddsSuppression requestId suffix initial
pruneAddsSuppression (action :: rest) suffix requestId initial =
  lengthPrefixPreservesSuccessor
    (diagnosticFor action initial)
    (pruneAddsSuppression rest suffix requestId
      (applyAction referenceModel action initial))

||| Every permitted rewrite removes exactly one suppression diagnostic from
||| reference execution.
public export
rewriteDiagnosticAccounting :
  RewriteEvidence before after -> (initial : SchedulerState) ->
  length (collectDiagnostics before initial) =
  S (length (collectDiagnostics after initial))
rewriteDiagnosticAccounting
  (PruneRedundant leading suffix
    (SameAtMostOnceEvaluation requestId)) initial =
      pruneAddsSuppression leading suffix requestId initial

||| Diagnostic loss across a derivation is exactly its number of rewrites.
public export
derivationDiagnosticAccounting :
  (witness : Derivation before after) -> (initial : SchedulerState) ->
  length (collectDiagnostics before initial) =
  length (trace witness) + length (collectDiagnostics after initial)
derivationDiagnosticAccounting Done initial = Refl
derivationDiagnosticAccounting (Then step later) initial =
  trans
    (rewriteDiagnosticAccounting step initial)
    (cong S (derivationDiagnosticAccounting later initial))

||| Execution keeps effective state and explanatory diagnostics separate.
public export
record Execution where
  constructor MkExecution
  effective : SchedulerState
  diagnostics : List Diagnostic

public export
Eq Execution where
  left == right =
    effective left == effective right && diagnostics left == diagnostics right

public export
Show Execution where
  show execution =
    "Execution(effective=" ++ show (effective execution) ++
    ", diagnostics=" ++ show (diagnostics execution) ++ ")"

||| Execute with diagnostics; diagnostics do not participate in interpretation.
public export
execute : List Action -> SchedulerState -> Execution
execute actions initial =
  MkExecution
    (interpret referenceModel actions initial)
    (collectDiagnostics actions initial)

||| Every at-most-once attempt is accounted for exactly once: it either adds
||| one identity to the seen set or emits one suppression diagnostic.
public export
atMostOnceAttemptAccounting :
  (actions : List Action) -> (initial : SchedulerState) ->
  length (seenAtMostOnce (effective (execute actions initial))) +
    length (diagnostics (execute actions initial)) =
  length (seenAtMostOnce initial) + countAtMostOnceAttempts actions
atMostOnceAttemptAccounting [] initial = Refl
atMostOnceAttemptAccounting (ReadMemory :: rest)
  (MkSchedulerState seen effective reads sandboxes) =
    atMostOnceAttemptAccounting rest
      (MkSchedulerState seen effective (S reads) sandboxes)
atMostOnceAttemptAccounting
  (ScheduleEvaluation attemptId Repeatable :: rest)
  (MkSchedulerState seen effective reads sandboxes) =
    atMostOnceAttemptAccounting rest
      (MkSchedulerState
        seen
        (effective ++ [MkScheduledRequest attemptId Repeatable])
        reads sandboxes)
atMostOnceAttemptAccounting
  (ScheduleEvaluation attemptId AtMostOnce :: rest)
  (MkSchedulerState seen effective reads sandboxes) with
    (classifyAtMostOnce attemptId
      (MkSchedulerState seen effective reads sandboxes))
  atMostOnceAttemptAccounting
    (ScheduleEvaluation attemptId AtMostOnce :: rest)
    (MkSchedulerState seen effective reads sandboxes) |
      AcceptedAttempt notSeen transition noDiagnostic =
        rewrite transition in
        rewrite noDiagnostic in
        trans
          (atMostOnceAttemptAccounting rest
            (acceptedState attemptId
              (MkSchedulerState seen effective reads sandboxes)))
          (sym (plusSuccRight (length seen)
            (countAtMostOnceAttempts rest)))
  atMostOnceAttemptAccounting
    (ScheduleEvaluation attemptId AtMostOnce :: rest)
    (MkSchedulerState seen effective reads sandboxes) |
      SuppressedAttempt alreadySeen transition suppressionDiagnostic =
        rewrite transition in
        rewrite suppressionDiagnostic in
        let inductionResult = atMostOnceAttemptAccounting rest
              (MkSchedulerState seen effective reads sandboxes)
         in trans
              (plusSuccRight
                (length (seenAtMostOnce
                  (interpret PhiLam.ReferenceScheduler.referenceModel rest
                    (MkSchedulerState seen effective reads sandboxes))))
                (length (collectDiagnostics rest
                  (MkSchedulerState seen effective reads sandboxes))))
              (trans
                (cong S inductionResult)
                (sym (plusSuccRight
                  (length seen)
                  (countAtMostOnceAttempts rest))))
atMostOnceAttemptAccounting (CallSandbox :: rest)
  (MkSchedulerState seen effective reads sandboxes) =
    atMostOnceAttemptAccounting rest
      (MkSchedulerState seen effective reads (S sandboxes))

||| Normalization removes exactly one reference suppression diagnostic for
||| every recorded rewrite. Effective semantics remain equal separately.
public export
normalizationDiagnosticAccounting :
  (actions : List Action) -> (initial : SchedulerState) ->
  length (diagnostics (execute actions initial)) =
  length (audit (normalize actions)) +
    length
      (diagnostics
        (execute (normalized (normalize actions)) initial))
normalizationDiagnosticAccounting actions initial =
  derivationDiagnosticAccounting
    (derivation (normalize actions)) initial

||| The execution API and abstract interpreter share exactly one effective path.
public export
executionAgreesWithInterpreter :
  (actions : List Action) -> (initial : SchedulerState) ->
  effective (execute actions initial) =
  interpret PhiLam.ReferenceScheduler.referenceModel actions initial
executionAgreesWithInterpreter _ _ = Refl

||| Instrumented execution preserves the same scheduler invariant as the
||| underlying interpreter; diagnostics cannot corrupt effective state.
public export
executionPreservesWellFormed :
  (actions : List Action) -> (initial : SchedulerState) ->
  WellFormed initial ->
  WellFormed (effective (execute actions initial))
executionPreservesWellFormed actions initial coherent =
  interpretPreservesWellFormed actions initial coherent

||| Every execution from the public empty state produces coherent state.
public export
executionFromEmptyWellFormed :
  (actions : List Action) ->
  WellFormed
    (effective
      (execute actions PhiLam.ReferenceScheduler.emptyState))
executionFromEmptyWellFormed actions =
  executionPreservesWellFormed
    actions
    PhiLam.ReferenceScheduler.emptyState
    emptyWellFormed
