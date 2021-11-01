
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

def transform : PureFiniteType → FiniteType
 | PureFiniteType.zero => FiniteType.zero
 | PureFiniteType.application ρ => (transform ρ) ↣ FiniteType.zero

#eval transform (PureFiniteType.application (PureFiniteType.application PureFiniteType.zero))

def getPFT (n : Nat) : PureFiniteType :=
  match n with
    | Nat.zero => PureFiniteType.zero
    | Nat.succ n => PureFiniteType.application (getPFT n)

#eval getPFT 2

instance : Coe PureFiniteType FiniteType := ⟨transform⟩

instance : OfNat FiniteType n := ⟨getPFT n⟩

example (n : Nat) : FiniteType.deg (transform (getPFT n)) = n :=
  Nat.recOn (motive := fun x => FiniteType.deg (transform (getPFT x)) = x) n
    rfl
    (fun n ih => show FiniteType.deg (transform (getPFT (Nat.succ n))) = (Nat.succ n) from
    calc FiniteType.deg (transform (getPFT (Nat.succ n))) = Nat.succ (FiniteType.deg (transform (getPFT (n)))) := rfl
          _ = Nat.succ n := by rw [ih]
    )

