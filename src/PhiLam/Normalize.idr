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

||| Runtime projection of a typed rewrite step.
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

||| Proof that one rewrite transforms exactly `before` into `after`.
|||
||| The constructor can only remove the second of two adjacent evaluations.
||| Its leading context and suffix make both lists explicit in the type.
public export
data RewriteEvidence : (before : List Action) -> (after : List Action) -> Type where
  PruneEvaluation : (leading : List Action) ->
    (suffix : List Action) ->
    RewriteEvidence
      (leading ++ EvaluateLLM :: EvaluateLLM :: suffix)
      (leading ++ EvaluateLLM :: suffix)

||| A type-aligned sequence of rewrites from `before` to `after`.
public export
data Derivation : (before : List Action) -> (after : List Action) -> Type where
  Done : Derivation actions actions
  Then : RewriteEvidence before middle -> Derivation middle after ->
         Derivation before after

liftRewrite : (action : Action) -> RewriteEvidence before after ->
              RewriteEvidence (action :: before) (action :: after)
liftRewrite action (PruneEvaluation leading suffix) =
  PruneEvaluation (action :: leading) suffix

liftDerivation : (action : Action) -> Derivation before after ->
                 Derivation (action :: before) (action :: after)
liftDerivation _ Done = Done
liftDerivation action (Then step later) =
  Then (liftRewrite action step) (liftDerivation action later)

rewriteStep : RewriteEvidence before after -> Step
rewriteStep (PruneEvaluation leading _) =
  MkStep PruneRedundantEvaluation (S (length leading))

||| Erase the dependent proof into a human-readable audit trace.
public export
trace : Derivation before after -> List Step
trace Done = []
trace (Then step later) = rewriteStep step :: trace later

||| Evidence that the first list occurs in order within the second list.
public export
data Subsequence : List element -> List element -> Type where
  SubRefl : Subsequence items items
  SubNil : Subsequence [] larger
  SubKeep : Subsequence smaller larger ->
            Subsequence (item :: smaller) (item :: larger)
  SubDrop : Subsequence smaller larger ->
            Subsequence smaller (item :: larger)

sameSequence : (items : List element) -> Subsequence items items
sameSequence [] = SubNil
sameSequence (_ :: rest) = SubKeep (sameSequence rest)

subsequenceTransitive : Subsequence first second ->
                        Subsequence second third ->
                        Subsequence first third
subsequenceTransitive SubRefl right = right
subsequenceTransitive left SubRefl = left
subsequenceTransitive SubNil _ = SubNil
subsequenceTransitive left (SubDrop right) =
  SubDrop (subsequenceTransitive left right)
subsequenceTransitive (SubKeep left) (SubKeep right) =
  SubKeep (subsequenceTransitive left right)
subsequenceTransitive (SubDrop left) (SubKeep right) =
  SubDrop (subsequenceTransitive left right)

prunePreservesOrder : (leading : List Action) -> (suffix : List Action) ->
  Subsequence
    (leading ++ EvaluateLLM :: suffix)
    (leading ++ EvaluateLLM :: EvaluateLLM :: suffix)
prunePreservesOrder [] suffix =
  SubKeep (SubDrop (sameSequence suffix))
prunePreservesOrder (_ :: rest) suffix =
  SubKeep (prunePreservesOrder rest suffix)

rewritePreservesOrder : RewriteEvidence before after ->
                        Subsequence after before
rewritePreservesOrder (PruneEvaluation leading suffix) =
  prunePreservesOrder leading suffix

||| A derivation can remove actions, but cannot invent or reorder them.
public export
derivationPreservesOrder : Derivation before after ->
                           Subsequence after before
derivationPreservesOrder Done = SubRefl
derivationPreservesOrder (Then step later) =
  subsequenceTransitive
    (derivationPreservesOrder later)
    (rewritePreservesOrder step)

||| A certificate that a sequence contains no adjacent evaluations.
public export
data NormalForm : List Action -> Type where
  NormalNil : NormalForm []
  NormalRead : NormalForm rest -> NormalForm (ReadMemory :: rest)
  NormalSandbox : NormalForm rest -> NormalForm (CallSandbox :: rest)
  NormalEvaluation : NormalForm [EvaluateLLM]
  NormalEvaluationRead : NormalForm (ReadMemory :: rest) ->
    NormalForm (EvaluateLLM :: ReadMemory :: rest)
  NormalEvaluationSandbox : NormalForm (CallSandbox :: rest) ->
    NormalForm (EvaluateLLM :: CallSandbox :: rest)

||| The normal form, a type-aligned derivation, and its normal-form proof.
public export
record Normalization (input : List Action) where
  constructor MkNormalization
  normalized : List Action
  derivation : Derivation input normalized
  certificate : NormalForm normalized

public export
audit : Normalization input -> List Step
audit result = trace (derivation result)

||| Collapse adjacent duplicate evaluations and retain typed evidence.
public export
normalize : (actions : List Action) -> Normalization actions
normalize [] = MkNormalization [] Done NormalNil
normalize (ReadMemory :: rest) =
  let later = normalize rest
   in MkNormalization
        (ReadMemory :: normalized later)
        (liftDerivation ReadMemory (derivation later))
        (NormalRead (certificate later))
normalize (CallSandbox :: rest) =
  let later = normalize rest
   in MkNormalization
        (CallSandbox :: normalized later)
        (liftDerivation CallSandbox (derivation later))
        (NormalSandbox (certificate later))
normalize [EvaluateLLM] =
  MkNormalization [EvaluateLLM] Done NormalEvaluation
normalize (EvaluateLLM :: EvaluateLLM :: rest) =
  let later = normalize (EvaluateLLM :: rest)
   in MkNormalization
        (normalized later)
        (Then (PruneEvaluation [] rest) (derivation later))
        (certificate later)
normalize (EvaluateLLM :: ReadMemory :: rest) =
  let later = normalize rest
   in MkNormalization
        (EvaluateLLM :: ReadMemory :: normalized later)
        (liftDerivation EvaluateLLM
          (liftDerivation ReadMemory (derivation later)))
        (NormalEvaluationRead (NormalRead (certificate later)))
normalize (EvaluateLLM :: CallSandbox :: rest) =
  let later = normalize rest
   in MkNormalization
        (EvaluateLLM :: CallSandbox :: normalized later)
        (liftDerivation EvaluateLLM
          (liftDerivation CallSandbox (derivation later)))
        (NormalEvaluationSandbox (NormalSandbox (certificate later)))

||| The output of normalization is an order-preserving subsequence of input.
public export
normalizationPreservesOrder : (actions : List Action) ->
  Subsequence (normalized (normalize actions)) actions
normalizationPreservesOrder actions =
  derivationPreservesOrder (derivation (normalize actions))

||| Executable normal-form predicate used at untyped boundaries.
public export
isNormal : List Action -> Bool
isNormal [] = True
isNormal (ReadMemory :: rest) = isNormal rest
isNormal (CallSandbox :: rest) = isNormal rest
isNormal [EvaluateLLM] = True
isNormal (EvaluateLLM :: EvaluateLLM :: _) = False
isNormal (EvaluateLLM :: ReadMemory :: rest) = isNormal rest
isNormal (EvaluateLLM :: CallSandbox :: rest) = isNormal rest

||| A normal-form certificate is sound with respect to `isNormal`.
public export
normalFormSound : NormalForm actions -> isNormal actions = True
normalFormSound NormalNil = Refl
normalFormSound (NormalRead later) = normalFormSound later
normalFormSound (NormalSandbox later) = normalFormSound later
normalFormSound NormalEvaluation = Refl
normalFormSound (NormalEvaluationRead later) = normalFormSound later
normalFormSound (NormalEvaluationSandbox later) = normalFormSound later

||| Every result produced by `normalize` satisfies the normal-form predicate.
public export
normalizedIsNormal : (actions : List Action) ->
                     isNormal (normalized (normalize actions)) = True
normalizedIsNormal actions = normalFormSound (certificate (normalize actions))

||| Normalizing a certified normal form leaves it unchanged.
public export
normalFormFixed : (witness : NormalForm actions) ->
                  normalized (normalize actions) = actions
normalFormFixed NormalNil = Refl
normalFormFixed (NormalRead later) =
  cong (ReadMemory ::) (normalFormFixed later)
normalFormFixed (NormalSandbox later) =
  cong (CallSandbox ::) (normalFormFixed later)
normalFormFixed NormalEvaluation = Refl
normalFormFixed (NormalEvaluationRead later) =
  cong (EvaluateLLM ::) (normalFormFixed later)
normalFormFixed (NormalEvaluationSandbox later) =
  cong (EvaluateLLM ::) (normalFormFixed later)

||| Normalization is idempotent: a second pass cannot change its output.
public export
normalizeIdempotent : (actions : List Action) ->
  normalized (normalize (normalized (normalize actions))) =
  normalized (normalize actions)
normalizeIdempotent actions =
  normalFormFixed (certificate (normalize actions))
