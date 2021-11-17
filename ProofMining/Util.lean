

class Mem (α : outParam $ Type u) (γ : Type v) where
  mem : α → γ → Prop

infix:50 " ∈ " => Mem.mem

/-
  Missing stuff about lists.
  Much of this is translated ad litteram from Lean3 mathlib
-/

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

  inductive Sublist : List α → List α → Prop 
  | slnil : Sublist [] []
  | cons : Sublist x y → Sublist x (a :: y)
  | cons₂ : Sublist x y → Sublist (a :: x) (a :: y)

  infix:50 " <+ " => Sublist