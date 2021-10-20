
inductive FiniteType where
| zero : FiniteType
| application : FiniteType → FiniteType → FiniteType
deriving Repr

namespace FiniteType

infixl:60 "↣" => application

def deg : FiniteType -> Nat
  | FiniteType.zero => 0
  | FiniteType.application ρ τ => Nat.max (deg τ) ((deg ρ) + 1)

#eval FiniteType.deg (FiniteType.zero ↣ FiniteType.zero ↣ FiniteType.zero ↣ FiniteType.zero)

end FiniteType

inductive PureFiniteType where
| zero : PureFiniteType
| application : PureFiniteType → PureFiniteType
deriving Repr

def transfrom : PureFiniteType → FiniteType
 | PureFiniteType.zero => FiniteType.zero
 | PureFiniteType.application ρ => (transfrom ρ) ↣ FiniteType.zero

#eval transfrom (PureFiniteType.application (PureFiniteType.application PureFiniteType.zero))

def getPFT (n : Nat) : PureFiniteType :=
  match n with
    | Nat.zero => PureFiniteType.zero
    | Nat.succ n => PureFiniteType.application (getPFT n)

#eval getPFT 2