-- SPDX-License-Identifier: MPL-2.0

import PhiLamFormal

namespace PhiLam.Vectors

def requestA : RequestId := ⟨0⟩
def requestB : RequestId := ⟨1⟩

def onceA : Action := .scheduleEvaluation requestA .atMostOnce
def onceB : Action := .scheduleEvaluation requestB .atMostOnce
def repeatA : Action := .scheduleEvaluation requestA .repeatable

def vocabulary : List Action :=
  [.readMemory, .callSandbox, onceA, onceB, repeatA]

def sequences : Nat → List (List Action)
  | 0 => [[]]
  | length + 1 =>
      vocabulary.flatMap fun action =>
        (sequences length).map (action :: ·)

def boundedSequences : List (List Action) :=
  sequences 0 ++ sequences 1 ++ sequences 2 ++
    sequences 3 ++ sequences 4

def isNormal : List Action → Bool
  | [] => true
  | [_] => true
  | first :: second :: rest =>
      !redundant first second && isNormal (second :: rest)

example :
    normalize [.readMemory, onceA, onceA, .callSandbox] =
      [.readMemory, onceA, .callSandbox] := by decide

example : normalize [onceA, onceB] = [onceA, onceB] := by decide
example : normalize [repeatA, repeatA] = [repeatA, repeatA] := by decide
example : normalize [onceA, repeatA] = [onceA, repeatA] := by decide
example : normalize [onceA, onceA, onceA] = [onceA] := by decide

example : boundedSequences.length = 781 := by native_decide

example :
    boundedSequences.all (fun actions => isNormal (normalize actions)) = true :=
  by native_decide

example :
    boundedSequences.all
      (fun actions => normalize (normalize actions) == normalize actions) = true :=
  by native_decide

end PhiLam.Vectors
