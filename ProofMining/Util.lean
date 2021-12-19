

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

  structure Embedding (xs ys : List α) where 
    emb : Nat → Nat 
    emb_ok : xs.nth i = some x → ys.nth i = some x
    

end List 

namespace Option 

  def get!! {α : Type _} [Inhabited α] : Option α → α
  | some x => x
  | none => Inhabited.default

end Option 


macro "TODO_ALEX" : term => `(sorry)
macro "TODO_ALEX" : tactic => `(sorry)

macro "TODO_HORATIU" : term => `(sorry)
macro "TODO_HORATIU" : tactic => `(sorry)