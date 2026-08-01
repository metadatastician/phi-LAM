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

||| The empty effective scheduler state.
public export
emptyState : SchedulerState
emptyState = MkSchedulerState [] [] 0 0

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

diagnosticFor : Action -> SchedulerState -> List Diagnostic
diagnosticFor (ScheduleEvaluation requestId AtMostOnce) state =
  if containsRequest requestId (seenAtMostOnce state)
    then [SuppressedDuplicate requestId]
    else []
diagnosticFor _ _ = []

collectDiagnostics : List Action -> SchedulerState -> List Diagnostic
collectDiagnostics [] _ = []
collectDiagnostics (action :: rest) state =
  diagnosticFor action state ++
  collectDiagnostics rest (applyAction referenceModel action state)

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

||| The execution API and abstract interpreter share exactly one effective path.
public export
executionAgreesWithInterpreter :
  (actions : List Action) -> (initial : SchedulerState) ->
  effective (execute actions initial) =
  interpret PhiLam.ReferenceScheduler.referenceModel actions initial
executionAgreesWithInterpreter _ _ = Refl
