-- SPDX-License-Identifier: MPL-2.0

module TestNormalize

import PhiLam.Action
import PhiLam.Normalize
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

exampleInput : List Action
exampleInput = [ReadMemory, EvaluateLLM, EvaluateLLM, CallSandbox]

actionVocabulary : List Action
actionVocabulary = [ReadMemory, EvaluateLLM, CallSandbox]

sequences : Nat -> List (List Action)
sequences Z = [[]]
sequences (S length) =
  concat (map (\action => map (action ::) (sequences length)) actionVocabulary)

boundedSequences : List (List Action)
boundedSequences =
  sequences 0 ++ sequences 1 ++ sequences 2 ++
  sequences 3 ++ sequences 4 ++ sequences 5

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

||| This definition typechecks only because the general idempotence theorem
||| specializes to the documented example.
exampleIdempotenceProof :
  normalized (normalize (normalized (normalize exampleInput))) =
  normalized (normalize exampleInput)
exampleIdempotenceProof =
  normalizeIdempotent
    [ReadMemory, EvaluateLLM, EvaluateLLM, CallSandbox]

main : IO ()
main = do
  let example = normalize exampleInput
  exampleOutput <- assertEqual "normalises the documented example"
                               [ReadMemory, EvaluateLLM, CallSandbox]
                               (normalized example)
  exampleTrace <- assertEqual "records typed evidence for the example"
                              [MkStep PruneRedundantEvaluation 2]
                              (audit example)
  unchanged <- assertEqual "leaves a normal sequence unchanged"
                           [ReadMemory, EvaluateLLM, CallSandbox]
                           (normalized
                             (normalize
                               [ReadMemory, EvaluateLLM, CallSandbox]))
  unchangedTrace <- assertEqual "normal input has an empty derivation"
                                []
                                (audit
                                  (normalize
                                    [ReadMemory, EvaluateLLM, CallSandbox]))
  triple <- assertEqual "records each dynamic rewrite in a run"
                        [ MkStep PruneRedundantEvaluation 1
                        , MkStep PruneRedundantEvaluation 1
                        ]
                        (audit
                          (normalize
                            [EvaluateLLM, EvaluateLLM, EvaluateLLM]))
  boundaries <- assertEqual "does not collapse separated evaluations"
                            [EvaluateLLM, ReadMemory, EvaluateLLM]
                            (normalized
                              (normalize
                                [EvaluateLLM, ReadMemory, EvaluateLLM]))
  exhaustiveNormal <- assertTrue
                        "all 364 sequences of length at most five normalize"
                        (all outputIsNormal boundedSequences)
  exhaustiveIdempotent <- assertTrue
                            "idempotence holds over the bounded corpus"
                            (all runtimeIdempotent boundedSequences)
  exhaustiveAccounting <- assertTrue
                            "every trace accounts for every removal"
                            (all traceAccountsForRemovals boundedSequences)
  let outcomes =
        [ exampleOutput
        , exampleTrace
        , unchanged
        , unchangedTrace
        , triple
        , boundaries
        , exhaustiveNormal
        , exhaustiveIdempotent
        , exhaustiveAccounting
        ]
  if all id outcomes
    then putStrLn "All 9 test groups passed."
    else exitWith (ExitFailure 1)
