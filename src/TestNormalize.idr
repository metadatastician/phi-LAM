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

exampleInput : List Action
exampleInput = [ReadMemory, EvaluateLLM, EvaluateLLM, CallSandbox]

exampleExpected : Normalization
exampleExpected =
  MkNormalization
    [ReadMemory, EvaluateLLM, CallSandbox]
    [MkStep PruneRedundantEvaluation 2]

tripleExpected : Normalization
tripleExpected =
  MkNormalization
    [EvaluateLLM]
    [ MkStep PruneRedundantEvaluation 1
    , MkStep PruneRedundantEvaluation 2
    ]

main : IO ()
main = do
  example <- assertEqual "normalises the documented example"
                         exampleExpected
                         (normalize exampleInput)
  unchanged <- assertEqual "leaves a normal sequence unchanged"
                           (MkNormalization
                             [ReadMemory, EvaluateLLM, CallSandbox]
                             [])
                           (normalize
                             [ReadMemory, EvaluateLLM, CallSandbox])
  triple <- assertEqual "records every removal in a run"
                        tripleExpected
                        (normalize [EvaluateLLM, EvaluateLLM, EvaluateLLM])
  boundaries <- assertEqual "does not collapse separated evaluations"
                            (MkNormalization
                              [EvaluateLLM, ReadMemory, EvaluateLLM]
                              [])
                            (normalize
                              [EvaluateLLM, ReadMemory, EvaluateLLM])
  if all id [example, unchanged, triple, boundaries]
    then putStrLn "All 4 tests passed."
    else exitWith (ExitFailure 1)
