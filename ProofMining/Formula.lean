import ProofMining.Term

/-
  THE COMMENTS BELOW NO LONGER APPLY. 
  THIS IS FOL.

  The type of propositional formulas.
  We have no terms and no atomic formulas beyond faslumat the moment, as they are irrelevant for proving propositional logic results.
  We will add them later.
  The same remark applies to constructors corresponding to quantifiers.
-/

inductive Formula
| equality : Term → Term → Formula
| conjunction : Formula → Formula → Formula
| disjunction : Formula → Formula → Formula
| implication : Formula → Formula → Formula
| falsum : Formula
| universal : FiniteType → Formula → Formula 
| existential : FiniteType → Formula → Formula 
deriving DecidableEq, Inhabited


namespace Formula
/-
  Familiar notations.
  Note that ⋀ and ⋁ bind stronger than ⟹ and that ⟹ is right-associative.
-/


infix:100 "≅" => equality
infixl:55 " ⋀ " => conjunction --input with \ bigvee 
infixl:55 " ⋁ " => disjunction --input with \ bigwedge
infixr:50 " ⟹ " => implication --input with \ ==>
notation "∀∀" => universal
notation "∃∃" => existential

abbrev negation (A) := A ⟹ falsum

prefix:max "∼" => negation --input with \ ~

@[appUnexpander universal] def unexpandUniversal : Lean.PrettyPrinter.Unexpander 
| `(universal $ρ $A) => `(∀∀ $ρ $A)
| _ => throw ()

@[appUnexpander existential] def unexpandExistential : Lean.PrettyPrinter.Unexpander 
| `(existential $ρ $A) => `(∃∃ $ρ $A)
| _ => throw ()

-- useless
def shift (place : Nat) (cutoff : Nat := 0) : Formula → Formula := 
fun A => match cutoff, A with 
| c, t ≅ u => t.shift place c ≅ u.shift place c 
| c, A ⋀ B => A.shift place c ⋀ B.shift place c
| c, A ⋁ B => A.shift place c ⋁ B.shift place c
| c, A ⟹ B => A.shift place c ⟹ B.shift place c
| _, falsum => falsum
| c, universal ρ A => universal ρ $ A.shift place $ c + 1
| c, existential ρ A => existential ρ $ A.shift place $ c + 1

def subst : Formula → Nat → Term → Formula 
| t ≅ u, i, s => t.subst i s ≅ u.subst i s
| A ⋀ B, i, s => A.subst i s ⋀ B.subst i s
| A ⋁ B, i, s => A.subst i s ⋁ B.subst i s
| A ⟹ B, i, s => A.subst i s ⟹ B.subst i s
| falsum, _, _ => falsum
| universal ρ A, i, s => universal ρ $ A.subst (i + 1) (s.shift (place := 1))
| existential ρ A, i, s => existential ρ $ A.subst (i + 1) (s.shift (place := 1))

open Term in
inductive WellFormed : Environment → Formula → Prop 
| equality : WellTyped e t 0 → WellTyped e u 0 → WellFormed e (t ≅ u)
| conjunction (A B) : WellFormed e A → WellFormed e B → WellFormed e (A ⋀ B)
| disjunction (A B) : WellFormed e A → WellFormed e B → WellFormed e (A ⋁ B)
| implication (A B) : WellFormed e A → WellFormed e B → WellFormed e (A ⟹ B)
| universal (A) : WellFormed (ρ :: e) A → WellFormed e (∀∀ ρ A)
| existential (A) : WellFormed (ρ :: e) A → WellFormed e (∃∃ ρ A)

notation e "wf⊢" A:max => WellFormed e A

def highereq : FiniteType → Term → Term → Formula
| ρ ↣ τ, s, t => universal ρ (highereq τ (Term.app s $ Term.var $ τ.deg) (Term.app t $ Term.var $ τ.deg))
| 0, s, t => equality s t
