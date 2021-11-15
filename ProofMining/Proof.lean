import ProofMining.Formula
import ProofMining.Util

open Formula (falsum)

/-
  The type of propositional proofs. 
  `Proof Γ A` is to be read as the type of proofs of the formula A from the premises Γ.
  Each constructor correspons to an axiom or a rule of inference.
  We will add more constructors to `Proof` as we extend the system beyond propositional logic.

  Note the presence of the additional constructor `premise` saying that a formula can always be trivially proved when it is taken as a premise.
-/

inductive Proof (Γ : List Formula) : Formula →  Type
| contrConj (A : Formula) : Proof Γ (A ⟹ A ⋀ A)
| contrDisj (A : Formula) : Proof Γ (A ⋁ A ⟹ A)
| weakConj (A B : Formula) : Proof Γ (A ⋀ B ⟹ A)
| weakDisj (A B : Formula) : Proof Γ (A ⟹ A ⋁ B)
| permConj (A B : Formula) : Proof Γ (A ⋀ B ⟹ B ⋀ A)
| permDisj (A B : Formula) : Proof Γ (A ⋁ B ⟹ B ⋁ A)
| exFalso (A : Formula) : Proof Γ (falsum ⟹ A)
| universalAxiom (ρ : FiniteType) (A : Formula) (t : Term) : Proof Γ (∀∀ ρ A ⟹ Formula.subst A 0 t)
| existentialAxiom (ρ : FiniteType) (A : Formula) (t : Term) : Proof Γ (Formula.subst A 0 t ⟹ ∃∃ ρ A)
| mpon {A B : Formula} : Proof Γ A → Proof Γ (A ⟹ B) → Proof Γ B
| syllogism {A B C : Formula} : Proof Γ (A ⟹ B) → Proof Γ (B ⟹ C) → Proof Γ (A ⟹ C)
| exportation {A B C : Formula} : Proof Γ (A ⋀ B ⟹ C) → Proof Γ (A ⟹ B ⟹ C)
| importation {A B C : Formula} : Proof Γ (A ⟹ B ⟹ C) → Proof Γ (A ⋀ B ⟹ C)
| expansion {A B : Formula} (C : Formula) : Proof Γ (A ⟹ B) → Proof Γ (C ⋁ A ⟹ C ⋁ B)
| universalRule {A B : Formula} (ρ : FiniteType) : Proof Γ (B ⟹ A) →  Proof Γ (B ⟹ ∀∀ ρ A)
| existentialRule {A B : Formula} (ρ : FiniteType) : Proof Γ (A ⟹ B) →  Proof Γ (∃∃ ρ A ⟹ B)
| premise {A : Formula} : A ∈ Γ → Proof Γ A


namespace Proof

section 
  variable {Γ : List Formula} {A B C : Formula}

  /-
    Duplicates of the constructors of `Proof`, but with all arguments implicit.
    In many cases, Lean will be able to infer the arguments of the constructors of `Proof`
    so we might as well avoid having to write them.
    TODO: Decide which is better.
  -/
  def contrConj' := @contrConj Γ A
  def contrDisj' := @contrDisj Γ A
  def weakConj' := @weakConj Γ A B 
  def weakDisj' := @weakDisj Γ A B
  def permConj' := @permConj Γ A B 
  def permDisj' := @permDisj Γ A B
  def exFalso' := @exFalso Γ A 
  def expansion' := @expansion Γ A B C

end

namespace Proof
/-
  Γ ⊢ A as a notation for Proof Γ A 
-/
infix:30 "⊢" => Proof





section DemoExamples

variable (A B : Formula) (Γ : List Formula)

/-
  ### Example 1: The propositional theorem "A implies A"
    All the proofs are the same, only written in different levels of detail or with different notations,
    for exemplification purposes only.
-/

  example : Proof Γ (A ⟹ A) :=
    let p₁ : Proof Γ (A ⟹ A ⋀ A) := contrConj A 
    let p₂ : Proof Γ (A ⋀ A ⟹ A) := weakConj A A 
    syllogism p₁ p₂

  example : Proof Γ (A ⟹ A) :=
    let p₁ : Proof Γ (A ⟹ A ⋀ A) := contrConj _ 
    let p₂ : Proof Γ (A ⋀ A ⟹ A) := weakConj _ _ 
    syllogism p₁ p₂

  example : Proof Γ (A ⟹ A) := 
    let p₁ : Proof Γ (A ⟹ A ⋀ A) := contrConj'
    let p₂ : Proof Γ (A ⋀ A ⟹ A) := weakConj' 
    syllogism p₁ p₂

  example : Γ ⊢ A ⟹ A :=
    let p₁ : Γ ⊢ A ⟹ A ⋀ A := contrConj _ 
    let p₂ : Γ ⊢ A ⋀ A ⟹ A := weakConj _ _
    syllogism p₁ p₂

  example : Proof Γ (A ⟹ A) := syllogism (contrConj _) (weakConj _ _)

/-
  ### Example 2: The propositional rule "from A, one can deduce that B implies A"
  Written first in detail, then concisely
-/

example (h : Γ ⊢ A) : Γ ⊢ B ⟹ A :=
  let p₁ : Γ ⊢ A ⋀ B ⟹ A := weakConj' 
  let p₂ : Γ ⊢ A ⟹ (B ⟹ A) := exportation p₁ 
  mpon h p₂

example (h : Γ ⊢ A) : Γ ⊢ B ⟹ A := 
  mpon h (exportation weakConj')

end DemoExamples