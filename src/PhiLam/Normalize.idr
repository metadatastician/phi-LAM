-- SPDX-License-Identifier: MPL-2.0

module PhiLam.Normalize

import PhiLam.Action

%default total

||| A named rewrite rule. There is deliberately only one rule at present.
public export
data Rule = PruneRedundantEvaluation

public export
Eq Rule where
  PruneRedundantEvaluation == PruneRedundantEvaluation = True

public export
Show Rule where
  show PruneRedundantEvaluation = "PruneRedundantEvaluation"

||| Evidence that a rule was applied at a zero-based input position.
public export
record Step where
  constructor MkStep
  rule : Rule
  position : Nat

public export
Eq Step where
  left == right =
    rule left == rule right && position left == position right

public export
Show Step where
  show step = show (rule step) ++ "@" ++ show (position step)

||| The normal form and the ordered trace that produced it.
public export
record Normalization where
  constructor MkNormalization
  normalized : List Action
  derivation : List Step

public export
Eq Normalization where
  left == right =
    normalized left == normalized right &&
    derivation left == derivation right

public export
Show Normalization where
  show result =
    "normal form: " ++ show (normalized result) ++
    "; derivation: " ++ show (derivation result)

normalizeFrom : Nat -> List Action -> Normalization
normalizeFrom _ [] = MkNormalization [] []
normalizeFrom _ [action] = MkNormalization [action] []
normalizeFrom index (EvaluateLLM :: EvaluateLLM :: rest) =
  let later = normalizeFrom (S index) (EvaluateLLM :: rest)
   in MkNormalization
        (normalized later)
        (MkStep PruneRedundantEvaluation (S index) :: derivation later)
normalizeFrom index (action :: rest) =
  let later = normalizeFrom (S index) rest
   in MkNormalization
        (action :: normalized later)
        (derivation later)

||| Collapse adjacent duplicate evaluations and retain a derivation trace.
public export
normalize : List Action -> Normalization
normalize = normalizeFrom 0
