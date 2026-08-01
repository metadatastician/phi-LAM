-- SPDX-License-Identifier: MPL-2.0

module TestNormalize

import PhiLam.Action
import PhiLam.Normalize
import PhiLam.ReferenceScheduler
import PhiLam.Semantics
import System

%default total

assertEqual : (Eq value, Show value) => String -> value -> value -> IO Bool
assertEqual label expected actual =
  if expected == actual
    then do
      putStrLn ("PASS: " ++ label)
      pure True
    else do
      putStrLn ("FAIL: " ++ label)
      putStrLn ("  expected: " ++ show expected)
      putStrLn ("  actual:   " ++ show actual)
      pure False

assertTrue : String -> Bool -> IO Bool
assertTrue label actual = assertEqual label True actual

requestA : RequestId
requestA = MkRequestId 0

requestB : RequestId
requestB = MkRequestId 1

onceA : Action
onceA = ScheduleEvaluation requestA AtMostOnce

onceB : Action
onceB = ScheduleEvaluation requestB AtMostOnce

repeatA : Action
repeatA = ScheduleEvaluation requestA Repeatable

exampleInput : List Action
exampleInput = [ReadMemory, onceA, onceA, CallSandbox]

actionVocabulary : List Action
actionVocabulary = [ReadMemory, CallSandbox, onceA, onceB, repeatA]

sequences : Nat -> List (List Action)
sequences Z = [[]]
sequences (S length) =
  concat (map (\action => map (action ::) (sequences length)) actionVocabulary)

boundedSequences : List (List Action)
boundedSequences =
  sequences 0 ++ sequences 1 ++ sequences 2 ++
  sequences 3 ++ sequences 4

runtimeIdempotent : List Action -> Bool
runtimeIdempotent actions =
  normalized (normalize (normalized (normalize actions))) ==
  normalized (normalize actions)

outputIsNormal : List Action -> Bool
outputIsNormal actions = isNormal (normalized (normalize actions))

traceAccountsForRemovals : List Action -> Bool
traceAccountsForRemovals actions =
  length actions == length (normalized result) + length (audit result)
  where
    result : Normalization actions
    result = normalize actions

runtimeSemanticPreservation : List Action -> Bool
runtimeSemanticPreservation actions =
  interpret referenceModel actions emptyState ==
  interpret referenceModel (normalized (normalize actions)) emptyState

executionInterpreterAgreement : List Action -> Bool
executionInterpreterAgreement actions =
  effective (execute actions emptyState) ==
  interpret referenceModel actions emptyState

executionStateIsWellFormed : List Action -> Bool
executionStateIsWellFormed actions =
  isWellFormed (effective (execute actions emptyState))

executionCountersAreExact : List Action -> Bool
executionCountersAreExact actions =
  let final = effective (execute actions emptyState)
   in memoryReads final == countMemoryReads actions &&
      sandboxCalls final == countSandboxCalls actions

attemptsAreAccountedFor : List Action -> Bool
attemptsAreAccountedFor actions =
  let result = execute actions emptyState
   in length (seenAtMostOnce (effective result)) +
        length (diagnostics result) == countAtMostOnceAttempts actions

||| The general idempotence theorem specializes to the documented example.
exampleIdempotenceProof :
  normalized (normalize (normalized (normalize exampleInput))) =
  normalized (normalize exampleInput)
exampleIdempotenceProof = normalizeIdempotent
  [ReadMemory, onceA, onceA, CallSandbox]

main : IO ()
main = do
  let example = normalize exampleInput
  exampleOutput <- assertEqual "prunes the same at-most-once request"
                               [ReadMemory, onceA, CallSandbox]
                               (normalized example)
  exampleTrace <- assertEqual "records typed evidence for the example"
                              [MkStep PruneRedundantEvaluation 2]
                              (audit example)
  differentIds <- assertEqual "retains different request identities"
                              [onceA, onceB]
                              (normalized (normalize [onceA, onceB]))
  repeatable <- assertEqual "retains repeated repeatable requests"
                            [repeatA, repeatA]
                            (normalized (normalize [repeatA, repeatA]))
  mixedPolicies <- assertEqual "retains mixed replay policies"
                               [onceA, repeatA]
                               (normalized (normalize [onceA, repeatA]))
  triple <- assertEqual "records each dynamic rewrite in a run"
                        [ MkStep PruneRedundantEvaluation 1
                        , MkStep PruneRedundantEvaluation 1
                        ]
                        (audit (normalize [onceA, onceA, onceA]))
  exhaustiveNormal <- assertTrue
                        "all 781 bounded sequences normalize"
                        (all outputIsNormal boundedSequences)
  exhaustiveIdempotent <- assertTrue
                            "idempotence holds over the bounded corpus"
                            (all runtimeIdempotent boundedSequences)
  exhaustiveAccounting <- assertTrue
                            "every trace accounts for every removal"
                            (all traceAccountsForRemovals boundedSequences)
  exhaustiveSemantics <- assertTrue
                          "the reference scheduler preserves all bounded sequences"
                          (all runtimeSemanticPreservation boundedSequences)
  exhaustiveExecution <- assertTrue
                          "execution agrees with interpretation on every bounded sequence"
                          (all executionInterpreterAgreement boundedSequences)
  exhaustiveWellFormed <- assertTrue
                            "all bounded executions preserve scheduler coherence"
                            (all executionStateIsWellFormed boundedSequences)
  exhaustiveCounters <- assertTrue
                          "all bounded executions have exact effect counters"
                          (all executionCountersAreExact boundedSequences)
  exhaustiveAttempts <- assertTrue
                          "all bounded attempts are accepted or suppressed"
                          (all attemptsAreAccountedFor boundedSequences)
  adjacentExecution <- assertEqual
                         "the runtime suppresses an adjacent duplicate"
                         (MkExecution
                           (MkSchedulerState
                             [requestA]
                             [MkScheduledRequest requestA AtMostOnce]
                             0 0)
                           [SuppressedDuplicate requestA])
                         (execute [onceA, onceA] emptyState)
  nonAdjacentExecution <- assertEqual
                            "the runtime suppresses a non-adjacent duplicate"
                            (MkExecution
                              (MkSchedulerState
                                [requestA]
                                [MkScheduledRequest requestA AtMostOnce]
                                1 0)
                              [SuppressedDuplicate requestA])
                            (execute [onceA, ReadMemory, onceA] emptyState)
  distinctExecution <- assertEqual
                         "the runtime schedules distinct identities"
                         [ MkScheduledRequest requestA AtMostOnce
                         , MkScheduledRequest requestB AtMostOnce
                         ]
                         (effectiveSchedule
                           (effective (execute [onceA, onceB] emptyState)))
  repeatableExecution <- assertEqual
                           "the runtime retains repeatable attempts"
                           [ MkScheduledRequest requestA Repeatable
                           , MkScheduledRequest requestA Repeatable
                           ]
                           (effectiveSchedule
                             (effective
                               (execute [repeatA, repeatA] emptyState)))
  effectCounters <- assertEqual
                      "memory and sandbox effects remain observable"
                      (MkSchedulerState [] [] 2 1)
                      (effective
                        (execute
                          [ReadMemory, CallSandbox, ReadMemory]
                          emptyState))
  let outcomes =
        [ exampleOutput
        , exampleTrace
        , differentIds
        , repeatable
        , mixedPolicies
        , triple
        , exhaustiveNormal
        , exhaustiveIdempotent
        , exhaustiveAccounting
        , exhaustiveSemantics
        , exhaustiveExecution
        , exhaustiveWellFormed
        , exhaustiveCounters
        , exhaustiveAttempts
        , adjacentExecution
        , nonAdjacentExecution
        , distinctExecution
        , repeatableExecution
        , effectCounters
        ]
  if all id outcomes
    then putStrLn "All 19 test groups passed."
    else exitWith (ExitFailure 1)
