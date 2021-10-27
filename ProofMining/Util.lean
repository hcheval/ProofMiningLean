

class Mem (α : outParam $ Type u) (γ : Type v) where
  mem : α → γ → Prop

infix:50 " ∈ " => Mem.mem

namespace List

  def mem (a : α) : List α → Prop
  | [] => False
  | (b :: l) => a = b ∨ mem a l

  instance : Mem α (List α) := ⟨mem⟩

  instance {α : Type _} : Mem α (List α) := ⟨mem⟩

  def nth : List α → Nat → Option α 
  | [], _ => none
  | a :: _, 0 => a
  | _ :: l, n + 1 => nth l n

variable (f : Nat → Nat)
variable (n : Nat)

#check f (n)