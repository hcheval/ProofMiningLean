
inductive FiniteType where
| zero : FiniteType
| application : FiniteType β FiniteType β FiniteType
deriving Repr, DecidableEq, Inhabited


notation "π" => FiniteType.zero
infixr:60 " β£ " => FiniteType.application

def FiniteType.deg : FiniteType β Nat
  | FiniteType.zero => 0
  | FiniteType.application Ο Ο => Nat.max (deg Ο) ((deg Ο) + 1)

#eval FiniteType.deg (FiniteType.zero β£ FiniteType.zero β£ FiniteType.zero β£ FiniteType.zero)

inductive PureFiniteType where
| zero : PureFiniteType
| application : PureFiniteType β PureFiniteType
deriving Repr

def transform : PureFiniteType β FiniteType
 | PureFiniteType.zero => FiniteType.zero
 | PureFiniteType.application Ο => (transform Ο) β£ FiniteType.zero

#eval transform (PureFiniteType.application (PureFiniteType.application PureFiniteType.zero))

def getPFT (n : Nat) : PureFiniteType :=
  match n with
    | Nat.zero => PureFiniteType.zero
    | Nat.succ n => PureFiniteType.application (getPFT n)

#eval getPFT 2

instance : Coe PureFiniteType FiniteType := β¨transformβ©

instance : OfNat FiniteType n := β¨getPFT nβ©

example (n : Nat) : FiniteType.deg (transform (getPFT n)) = n :=
  Nat.recOn (motive := fun x => FiniteType.deg (transform (getPFT x)) = x) n
    rfl
    (fun n ih => show FiniteType.deg (transform (getPFT (Nat.succ n))) = (Nat.succ n) from
    calc FiniteType.deg (transform (getPFT (Nat.succ n))) = Nat.succ (FiniteType.deg (transform (getPFT (n)))) := rfl
          _ = Nat.succ n := by rw [ih]
    )

namespace FiniteType

-- @[simp] def noneToInvalid : Option FiniteType β FiniteType 
-- | Ο β£ Ο => Ο β£ Ο 
-- | π => π
-- | invalid => invalid
-- | none => invalid

@[simp] def isArrow : FiniteType β Bool 
| _ β£ _ => true 
| _ => false

@[simp] def getArrowSource? : FiniteType β Option FiniteType 
| Ο β£ Ο => Ο
| _ => none

@[simp] def getArrowTarget? : FiniteType β Option FiniteType
| Ο β£ Ο => Ο 
| _ => none

@[simp] def contains : FiniteType β FiniteType β Bool 
| Ο β£ Ο, Ο => if Ο = Ο || Ο = Ο then true else contains Ο Ο || contains Ο Ο
| π, π => true 
| _, _ => false

/-
  if `Ο` contains any occurrences of `invalid`, then return `invalid`, otherwise return `Ο`
-/
-- @[simp] def propagateInvalid : FiniteType β FiniteType := 
--   fun Ο => if Ο.contains invalid then invalid else Ο

-- @[simp] def isValid : FiniteType β Bool := 
--   fun Ο => !Ο.contains invalid


end FiniteType