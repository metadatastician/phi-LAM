-- SPDX-License-Identifier: MPL-2.0

module PhiLam.Action

import Decidable.Equality

%default total

zeroNotSuccessor : Z = S right -> Void
zeroNotSuccessor _ impossible

successorNotZero : S left = Z -> Void
successorNotZero _ impossible

decNat : (left : Nat) -> (right : Nat) -> Dec (left = right)
decNat Z Z = Yes Refl
decNat Z (S right) = No zeroNotSuccessor
decNat (S left) Z = No successorNotZero
decNat (S left) (S right) =
  case decNat left right of
    Yes Refl => Yes Refl
    No different => No (\Refl => different Refl)

||| Stable identity for one logical evaluation request.
public export
record RequestId where
  constructor MkRequestId
  value : Nat

public export
Eq RequestId where
  left == right = value left == value right

public export
DecEq RequestId where
  decEq (MkRequestId left) (MkRequestId right) =
    case decNat left right of
      Yes Refl => Yes Refl
      No different => No (\Refl => different Refl)

public export
Show RequestId where
  show requestId = "request-" ++ show (value requestId)

||| Whether scheduling the same logical request again is meaningful.
public export
data ReplayPolicy
  = AtMostOnce
  | Repeatable

public export
Eq ReplayPolicy where
  AtMostOnce == AtMostOnce = True
  Repeatable == Repeatable = True
  _ == _ = False

public export
Show ReplayPolicy where
  show AtMostOnce = "AtMostOnce"
  show Repeatable = "Repeatable"

||| Symbolic scheduler entries supported by the current semantic kernel.
public export
data Action
  = ReadMemory
  | ScheduleEvaluation RequestId ReplayPolicy
  | CallSandbox

public export
Eq Action where
  ReadMemory == ReadMemory = True
  ScheduleEvaluation leftId leftPolicy ==
    ScheduleEvaluation rightId rightPolicy =
      leftId == rightId && leftPolicy == rightPolicy
  CallSandbox == CallSandbox = True
  _ == _ = False

public export
Show Action where
  show ReadMemory = "ReadMemory"
  show (ScheduleEvaluation requestId policy) =
    "ScheduleEvaluation(" ++ show requestId ++ ", " ++ show policy ++ ")"
  show CallSandbox = "CallSandbox"
