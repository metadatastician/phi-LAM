-- SPDX-License-Identifier: MPL-2.0

module PhiLam.Normalize

import Decidable.Equality
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

||| Proof that two scheduler entries denote the same at-most-once request.
public export
data Redundant : Action -> Action -> Type where
  SameAtMostOnceEvaluation : (requestId : RequestId) -> Redundant
    (ScheduleEvaluation requestId AtMostOnce)
    (ScheduleEvaluation requestId AtMostOnce)

||| Decide whether a pair carries evidence permitting its removal.
public export
decRedundant : (first : Action) -> (second : Action) ->
               Dec (Redundant first second)
decRedundant (ScheduleEvaluation firstId AtMostOnce)
             (ScheduleEvaluation secondId AtMostOnce) =
  case decEq firstId secondId of
    Yes Refl => Yes (SameAtMostOnceEvaluation firstId)
    No different =>
      No (\(SameAtMostOnceEvaluation _) => different Refl)
decRedundant ReadMemory second = No noEvidence
  where
    noEvidence : Redundant ReadMemory second -> Void
    noEvidence _ impossible
decRedundant CallSandbox second = No noEvidence
  where
    noEvidence : Redundant CallSandbox second -> Void
    noEvidence _ impossible
decRedundant (ScheduleEvaluation requestId Repeatable) second = No noEvidence
  where
    noEvidence : Redundant
      (ScheduleEvaluation requestId Repeatable) second -> Void
    noEvidence _ impossible
decRedundant (ScheduleEvaluation requestId AtMostOnce) ReadMemory = No noEvidence
  where
    noEvidence : Redundant
      (ScheduleEvaluation requestId AtMostOnce) ReadMemory -> Void
    noEvidence _ impossible
decRedundant (ScheduleEvaluation requestId AtMostOnce) CallSandbox = No noEvidence
  where
    noEvidence : Redundant
      (ScheduleEvaluation requestId AtMostOnce) CallSandbox -> Void
    noEvidence _ impossible
decRedundant (ScheduleEvaluation requestId AtMostOnce)
             (ScheduleEvaluation secondId Repeatable) = No noEvidence
  where
    noEvidence : Redundant
      (ScheduleEvaluation requestId AtMostOnce)
      (ScheduleEvaluation secondId Repeatable) -> Void
    noEvidence _ impossible

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
public export
data RewriteEvidence : (before : List Action) ->
                       (after : List Action) -> Type where
  PruneRedundant : (leading : List Action) ->
                   (suffix : List Action) ->
                   Redundant first second ->
                   RewriteEvidence
                     (leading ++ first :: second :: suffix)
                     (leading ++ first :: suffix)

||| A type-aligned sequence of rewrites from `before` to `after`.
public export
data Derivation : (before : List Action) -> (after : List Action) -> Type where
  Done : Derivation actions actions
  Then : RewriteEvidence before middle -> Derivation middle after ->
         Derivation before after

liftRewrite : (action : Action) -> RewriteEvidence before after ->
              RewriteEvidence (action :: before) (action :: after)
liftRewrite action (PruneRedundant leading suffix evidence) =
  PruneRedundant (action :: leading) suffix evidence

liftDerivation : (action : Action) -> Derivation before after ->
                 Derivation (action :: before) (action :: after)
liftDerivation _ Done = Done
liftDerivation action (Then step later) =
  Then (liftRewrite action step) (liftDerivation action later)

rewriteStep : RewriteEvidence before after -> Step
rewriteStep (PruneRedundant leading _ _) =
  MkStep PruneRedundantEvaluation (S (length leading))

||| Erase the dependent proof into a human-readable audit trace.
public export
trace : Derivation before after -> List Step
trace Done = []
trace (Then step later) = rewriteStep step :: trace later

||| Every primitive rewrite removes exactly one action.
pruneRemovesOne :
  (leading : List Action) -> (first : Action) ->
  (second : Action) -> (suffix : List Action) ->
  length (leading ++ first :: second :: suffix) =
  S (length (leading ++ first :: suffix))
pruneRemovesOne [] first second suffix = Refl
pruneRemovesOne (action :: leading) first second suffix =
  cong S (pruneRemovesOne leading first second suffix)

public export
rewriteRemovesOne : RewriteEvidence before after ->
  length before = S (length after)
rewriteRemovesOne
  (PruneRedundant leading suffix (SameAtMostOnceEvaluation requestId)) =
    pruneRemovesOne
      leading
      (ScheduleEvaluation requestId AtMostOnce)
      (ScheduleEvaluation requestId AtMostOnce)
      suffix

||| The erased trace length exactly accounts for every derivation removal.
public export
derivationLengthAccounting : (witness : Derivation before after) ->
  length before = length (trace witness) + length after
derivationLengthAccounting Done = Refl
derivationLengthAccounting (Then step later) =
  trans
    (rewriteRemovesOne step)
    (cong S (derivationLengthAccounting later))

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

prunePreservesOrder : (leading : List Action) ->
                      (suffix : List Action) ->
                      (evidence : Redundant first second) ->
  Subsequence
    (leading ++ first :: suffix)
    (leading ++ first :: second :: suffix)
prunePreservesOrder [] suffix _ =
  SubKeep (SubDrop (sameSequence suffix))
prunePreservesOrder (_ :: rest) suffix evidence =
  SubKeep (prunePreservesOrder rest suffix evidence)

rewritePreservesOrder : RewriteEvidence before after ->
                        Subsequence after before
rewritePreservesOrder (PruneRedundant leading suffix evidence) =
  prunePreservesOrder leading suffix evidence

||| A derivation can remove actions, but cannot invent or reorder them.
public export
derivationPreservesOrder : Derivation before after ->
                           Subsequence after before
derivationPreservesOrder Done = SubRefl
derivationPreservesOrder (Then step later) =
  subsequenceTransitive
    (derivationPreservesOrder later)
    (rewritePreservesOrder step)

||| A certificate that no adjacent pair carries redundancy evidence.
public export
data NormalForm : List Action -> Type where
  NormalNil : NormalForm []
  NormalOne : (action : Action) -> NormalForm [action]
  NormalCons : (first : Action) ->
               (second : Action) ->
               Not (Redundant first second) ->
               NormalForm (second :: rest) ->
               NormalForm (first :: second :: rest)

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

record NonEmptyNormalization (first : Action) (rest : List Action) where
  constructor MkNonEmptyNormalization
  normalizedTail : List Action
  nonEmptyDerivation :
    Derivation (first :: rest) (first :: normalizedTail)
  nonEmptyCertificate : NormalForm (first :: normalizedTail)

normalizeNonEmpty : (first : Action) -> (rest : List Action) ->
                    NonEmptyNormalization first rest
normalizeNonEmpty first [] =
  MkNonEmptyNormalization [] Done (NormalOne first)
normalizeNonEmpty first (second :: rest) with (decRedundant first second)
  normalizeNonEmpty first (second :: rest) | Yes evidence =
    let later = normalizeNonEmpty first rest
     in MkNonEmptyNormalization
          (normalizedTail later)
          (Then
            (PruneRedundant [] rest evidence)
            (nonEmptyDerivation later))
          (nonEmptyCertificate later)
  normalizeNonEmpty first (second :: rest) | No distinct =
    let later = normalizeNonEmpty second rest
     in MkNonEmptyNormalization
          (second :: normalizedTail later)
          (liftDerivation first (nonEmptyDerivation later))
          (NormalCons
            first
            second
            distinct
            (nonEmptyCertificate later))

||| Collapse adjacent identical at-most-once requests and retain typed evidence.
public export
normalize : (actions : List Action) -> Normalization actions
normalize [] = MkNormalization [] Done NormalNil
normalize (first :: rest) =
  let result = normalizeNonEmpty first rest
   in MkNormalization
        (first :: normalizedTail result)
        (nonEmptyDerivation result)
        (nonEmptyCertificate result)

||| Normalization's audit length exactly equals the number of removed actions.
public export
normalizationLengthAccounting : (actions : List Action) ->
  length actions =
  length (audit (normalize actions)) +
  length (normalized (normalize actions))
normalizationLengthAccounting actions =
  derivationLengthAccounting (derivation (normalize actions))

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
isNormal [action] = True
isNormal (first :: second :: rest) =
  case decRedundant first second of
    Yes _ => False
    No _ => isNormal (second :: rest)

||| A normal-form certificate is sound with respect to `isNormal`.
public export
normalFormSound : NormalForm actions -> isNormal actions = True
normalFormSound NormalNil = Refl
normalFormSound (NormalOne _) = Refl
normalFormSound (NormalCons first second distinct later) with
  (decRedundant first second)
  normalFormSound (NormalCons first second distinct later) |
    Yes evidence = void (distinct evidence)
  normalFormSound (NormalCons first second distinct later) |
    No _ = normalFormSound later

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
normalFormFixed (NormalOne _) = Refl
normalFormFixed (NormalCons first second distinct later) with
  (decRedundant first second)
  normalFormFixed (NormalCons first second distinct later) |
    Yes evidence = void (distinct evidence)
  normalFormFixed (NormalCons first second distinct later) |
    No _ = cong (first ::) (normalFormFixed later)

||| Normalization is idempotent: a second pass cannot change its output.
public export
normalizeIdempotent : (actions : List Action) ->
  normalized (normalize (normalized (normalize actions))) =
  normalized (normalize actions)
normalizeIdempotent actions =
  normalFormFixed (certificate (normalize actions))
