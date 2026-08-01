-- SPDX-License-Identifier: MPL-2.0

module TestNormalize

import PhiLam.Action
import PhiLam.Normalize
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

record ModelState where
  constructor MkModelState
  memoryReads : Nat
  repeatableEvaluations : Nat
  sandboxCalls : Nat
  lastAtMostOnce : Maybe RequestId

Eq ModelState where
  left == right =
    memoryReads left == memoryReads right &&
    repeatableEvaluations left == repeatableEvaluations right &&
    sandboxCalls left == sandboxCalls right &&
    lastAtMostOnce left == lastAtMostOnce right

Show ModelState where
  show state =
    "ModelState(" ++
    show (memoryReads state) ++ ", " ++
    show (repeatableEvaluations state) ++ ", " ++
    show (sandboxCalls state) ++ ", " ++
    show (lastAtMostOnce state) ++ ")"

readModel : ModelState -> ModelState
readModel (MkModelState reads repeats sandboxes last) =
  MkModelState (S reads) repeats sandboxes last

scheduleModel : RequestId -> ReplayPolicy -> ModelState -> ModelState
scheduleModel requestId AtMostOnce
  (MkModelState reads repeats sandboxes _) =
    MkModelState reads repeats sandboxes (Just requestId)
scheduleModel _ Repeatable
  (MkModelState reads repeats sandboxes last) =
    MkModelState reads (S repeats) sandboxes last

sandboxModel : ModelState -> ModelState
sandboxModel (MkModelState reads repeats sandboxes last) =
  MkModelState reads repeats (S sandboxes) last

atMostOnceLaw : (requestId : RequestId) -> (initial : ModelState) ->
  scheduleModel requestId AtMostOnce
    (scheduleModel requestId AtMostOnce initial) =
  scheduleModel requestId AtMostOnce initial
atMostOnceLaw _ (MkModelState _ _ _ _) = Refl

model : SchedulerModel ModelState
model = MkSchedulerModel
  readModel scheduleModel sandboxModel atMostOnceLaw

initialState : ModelState
initialState = MkModelState 0 0 0 Nothing

runtimeSemanticPreservation : List Action -> Bool
runtimeSemanticPreservation actions =
  interpret model actions initialState ==
  interpret model (normalized (normalize actions)) initialState

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
                          "the test model agrees on every bounded sequence"
                          (all runtimeSemanticPreservation boundedSequences)
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
        ]
  if all id outcomes
    then putStrLn "All 10 test groups passed."
    else exitWith (ExitFailure 1)
