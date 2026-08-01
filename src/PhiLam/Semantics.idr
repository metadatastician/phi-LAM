-- SPDX-License-Identifier: MPL-2.0

module PhiLam.Semantics

import PhiLam.Action
import PhiLam.Normalize

%default total

||| An abstract interpretation of scheduler entries over a caller-owned state.
|||
||| The single required law states what `AtMostOnce` means: applying the same
||| logical request twice has exactly the effect of applying it once.
public export
record SchedulerModel state where
  constructor MkSchedulerModel
  readMemory : state -> state
  scheduleEvaluation : RequestId -> ReplayPolicy -> state -> state
  callSandbox : state -> state
  atMostOnceIdempotent : (requestId : RequestId) -> (initial : state) ->
    scheduleEvaluation requestId AtMostOnce
      (scheduleEvaluation requestId AtMostOnce initial) =
    scheduleEvaluation requestId AtMostOnce initial

||| Interpret one symbolic scheduler entry in a model.
public export
applyAction : SchedulerModel state -> Action -> state -> state
applyAction model ReadMemory = readMemory model
applyAction model (ScheduleEvaluation requestId policy) =
  scheduleEvaluation model requestId policy
applyAction model CallSandbox = callSandbox model

||| Interpret a sequence from left to right.
public export
interpret : SchedulerModel state -> List Action -> state -> state
interpret _ [] initial = initial
interpret model (action :: rest) initial =
  interpret model rest (applyAction model action initial)

prunePreservesSemantics :
  (model : SchedulerModel state) ->
  (leading : List Action) ->
  (suffix : List Action) ->
  (evidence : Redundant first second) ->
  (initial : state) ->
  interpret model (leading ++ first :: second :: suffix) initial =
  interpret model (leading ++ first :: suffix) initial
prunePreservesSemantics model [] suffix
  (SameAtMostOnceEvaluation requestId) initial =
    cong
      (interpret model suffix)
      (atMostOnceIdempotent model requestId initial)
prunePreservesSemantics model (action :: rest) suffix evidence initial =
  prunePreservesSemantics
    model rest suffix evidence (applyAction model action initial)

||| Every permitted rewrite preserves every conforming scheduler model.
public export
rewritePreservesSemantics :
  (model : SchedulerModel state) ->
  RewriteEvidence before after ->
  (initial : state) ->
  interpret model before initial = interpret model after initial
rewritePreservesSemantics model
  (PruneRedundant leading suffix evidence) initial =
    prunePreservesSemantics model leading suffix evidence initial

||| A type-aligned chain of rewrites preserves scheduler interpretation.
public export
derivationPreservesSemantics :
  (model : SchedulerModel state) ->
  Derivation before after ->
  (initial : state) ->
  interpret model before initial = interpret model after initial
derivationPreservesSemantics _ Done _ = Refl
derivationPreservesSemantics model (Then step later) initial =
  trans
    (rewritePreservesSemantics model step initial)
    (derivationPreservesSemantics model later initial)

||| Normalization preserves interpretation for every conforming model.
public export
normalizePreservesSemantics :
  (model : SchedulerModel state) ->
  (actions : List Action) ->
  (initial : state) ->
  interpret model actions initial =
  interpret model (normalized (normalize actions)) initial
normalizePreservesSemantics model actions initial =
  derivationPreservesSemantics
    model (derivation (normalize actions)) initial
