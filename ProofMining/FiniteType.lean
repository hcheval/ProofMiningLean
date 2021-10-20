
inductive FiniteType where
| zero : FiniteType
| application : FiniteType → FiniteType → FiniteType

namespace FiniteType

infixl:60 "↣" => application

def deg : FiniteType -> Nat
  | FiniteType.zero => 0
  | FiniteType.application ρ τ => Nat.max (deg τ) ((deg ρ) + 1)


#eval FiniteType.deg (FiniteType.zero ↣ FiniteType.zero ↣ (FiniteType.zero ↣ FiniteType.zero))

end FiniteType
