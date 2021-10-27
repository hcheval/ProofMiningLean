
inductive FiniteType where
| zero : FiniteType
| application : FiniteType → FiniteType → FiniteType
deriving Repr

infixr:60 "↣" => FiniteType.application

def FiniteType.deg : FiniteType → Nat
  | FiniteType.zero => 0
  | FiniteType.application ρ τ => Nat.max (deg τ) ((deg ρ) + 1)

#eval FiniteType.deg (FiniteType.zero ↣ FiniteType.zero ↣ FiniteType.zero ↣ FiniteType.zero)

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

example (n : Nat) : FiniteType.deg (transfrom (getPFT n)) = n :=
  Nat.recOn (motive := fun x => FiniteType.deg (transfrom (getPFT x)) = x) n
    rfl
    (fun n ih => show FiniteType.deg (transfrom (getPFT (Nat.succ n))) = (Nat.succ n) from
    calc FiniteType.deg (transfrom (getPFT (Nat.succ n))) = Nat.succ (FiniteType.deg (transfrom (getPFT (n)))) := rfl
          _ = Nat.succ n := by rw [ih]
    )