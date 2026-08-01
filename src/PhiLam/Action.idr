-- SPDX-License-Identifier: MPL-2.0

module PhiLam.Action

%default total

||| The complete action vocabulary supported by the first semantic seed.
public export
data Action
  = ReadMemory
  | EvaluateLLM
  | CallSandbox

public export
Eq Action where
  ReadMemory == ReadMemory = True
  EvaluateLLM == EvaluateLLM = True
  CallSandbox == CallSandbox = True
  _ == _ = False

public export
Show Action where
  show ReadMemory = "ReadMemory"
  show EvaluateLLM = "EvaluateLLM"
  show CallSandbox = "CallSandbox"
