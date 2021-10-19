-- Chapter 9.3 From "Articol metateoreme"

import ProofMining.Proof
import ProofMining.Formula
import ProofMining.IntuitionisticRules

open Formula (falsum)
namespace Proof

theorem t19 (A B : Formula) : Γ ⊢ (A ⋀ B ⟹ B) := 
  let p₁ : Γ ⊢ (A ⋀ B ⟹ B ⋀ A) := permConj _ _
  let p₂ : Γ ⊢ (B ⋀ A ⟹ B) := weakConj _ _
  syllogism p₁ p₂

theorem t20 (A B : Formula) : Γ ⊢ (B ⟹ A ⋁ B) := 
  let p₁ : Γ ⊢ (B ⟹ B ⋁ A) := weakDisj _ _
  let p₂ : Γ ⊢ (B ⋁ A ⟹ A ⋁ B) := permDisj _ _
  syllogism p₁ p₂

theorem t21 (A : Formula) : Γ ⊢ A ⟹ A :=
  let p₁ : Γ ⊢ A ⟹ A ⋀ A := contrConj _ 
  let p₂ : Γ ⊢ A ⋀ A ⟹ A := weakConj _ _
  syllogism p₁ p₂

theorem t18 (A B : Formula) : Γ ⊢ (∼A ⋀ A ⟹ B) :=
  let p₁ : Γ ⊢ (falsum ⟹ B) := exFalso _
  let p₂ : Γ ⊢ ∼(∼A ⋀ A) := importation (t21 ∼A)
  syllogism p₂ p₁

theorem t22 (A B : Formula) : Γ ⊢ A ⟹ (B ⟹ (A ⋀ B)) :=
  let p₁ : Γ ⊢ (A ⋀ B) ⟹ (A ⋀ B) := t21 _
  exportation p₁

theorem t23 (A B : Formula) : Γ ⊢ A ⟹ (B ⟹ A) :=
  let p₁ : Γ ⊢ (A ⋀ B) ⟹ A := weakConj _ _
  exportation p₁

theorem t24 (A : Formula) : Γ ⊢ (A ⟹ ∼∼A) :=
  let p₁ : Γ ⊢ (A ⋀ ∼A ⟹ ∼A ⋀ A) := permConj _ _
  let p₂ : Γ ⊢ ∼(A ⋀ ∼A) := syllogism p₁ (t18 A falsum)
  exportation p₂

theorem t26a (A : Formula) : Γ ⊢ ∼A ⟹ ∼∼∼A :=
  t24 ∼A

theorem t26b (A : Formula) : Γ ⊢ ∼∼∼A ⟹ ∼A :=
  let p₁ : Γ ⊢ A ⟹ ∼∼∼∼A := syllogism (t24 _) (t24 _)
  let p₂ : Γ ⊢ ∼∼∼A ⋀ A ⟹ falsum := syllogism (permConj _ _) (importation p₁)
  exportation p₂

theorem t28a (A B : Formula) : Γ ⊢ ∼∼(A ⟹ B) ⟹ (∼∼A ⟹ ∼∼B) :=
  sorry

theorem t28b (A B : Formula) : Γ ⊢ (∼∼A ⟹ ∼∼B) ⟹ ∼∼(A ⟹ B) :=
  sorry

theorem t27a (A B : Formula) : Γ ⊢ ∼∼(A ⟹ B) ⟹ (A ⟹ ∼∼B) :=
  let p₀ : Γ ⊢ (∼∼(A ⟹ B)) ⋀ ∼∼A ⟹ ∼∼B := importation (t28a _ _)
  let p₁ : Γ ⊢ ∼∼A ⋀ (∼∼(A ⟹ B)) ⟹ (∼∼(A ⟹ B)) ⋀ ∼∼A := permConj _ _
  let p₂ : Γ ⊢ ∼∼A ⋀ (∼∼(A ⟹ B)) ⟹ ∼∼B := syllogism p₁ p₀
  let p₃ : Γ ⊢ ∼∼A ⟹ ∼∼(A ⟹ B) ⟹ ∼∼B := exportation p₂
  let p₄ : Γ ⊢ A ⟹ ∼∼(A ⟹ B) ⟹ ∼∼B := syllogism (t24 _) p₃
  exportation (syllogism (permConj _ _) (importation p₄))

theorem t27b (A B : Formula) : Γ ⊢ (A ⟹ ∼∼B) ⟹ ∼∼(A ⟹ B) :=
  sorry

theorem t29a (A B : Formula) : Γ ⊢ (A ⟹ ∼B) ⟹ (∼∼A ⟹ ∼B) :=
  let p₁ : Γ ⊢ (A ⟹ ∼B) ⟹ (∼∼A ⟹ ∼∼∼B) := syllogism (t24 _) (t28a _ _)
  let p₂ : Γ ⊢ (∼∼A ⟹ ∼∼∼B) ⟹ (∼∼A ⟹ ∼B) := exportation (syllogism (importation (t21 _)) (t26b _))
  syllogism p₁ p₂

theorem t29b (A B : Formula) : Γ ⊢ (∼∼A ⟹ ∼B) ⟹ (A ⟹ ∼B) :=
  sorry

theorem t30a (A B : Formula) : Γ ⊢ ∼∼(A ⋀ B) ⟹ (∼∼A ⋀ ∼∼B) :=
  sorry

theorem t30b (A B : Formula) : Γ ⊢ (∼∼A ⋀ ∼∼B) ⟹ ∼∼(A ⋀ B) :=
  sorry

theorem t31 (A B : Formula) : Γ ⊢ ∼∼(A ⋁ B) ⟹ ∼∼A ⟹ ∼∼B :=
  sorry

theorem t32a (A B : Formula) : Γ ⊢ ∼∼(A ⋁ B) ⟹ ∼∼(∼A ⋀ ∼B) :=
  sorry

theorem t32b (A B : Formula) : Γ ⊢ ∼(∼A ⋀ ∼B) ⟹ ∼∼(A ⋁ B) :=
  sorry

theorem t25 (A : Formula) : Γ ⊢ ∼∼(A ⋁ ∼A) := 
  let p₁ : Γ ⊢ ∼(∼A ⋀ ∼∼A) := syllogism (permConj _ _) (t18 _ _)
  mpon p₁ (t32b _ _)

theorem t33a (A B : Formula) : Γ ⊢ ∼(A ⋀ B) ⟹ A ⟹ ∼B :=
  let p₁ : Γ ⊢ ∼(A ⋀ B) ⋀ (A ⋀ B) ⟹ falsum := t18 _ _
  let p₂ : Γ ⊢ (B ⟹ ∼∼(A ⋀ B)) ⟹ ∼(A ⋀ B) ⟹ ∼B := sorry
  sorry

theorem t33b (A B : Formula) : Γ ⊢ (A ⟹ ∼B) ⟹ ∼(A ⋀ B) :=
  sorry

theorem t35 (A B : Formula) : Γ ⊢ A ⋁ B ⟹ ∼A ⟹ B :=
  let p₁ : Γ ⊢ ∼A ⋀ A ⟹ B := t18 _ _
  let p₂ : Γ ⊢ A ⟹ ∼A ⟹ B := exportation (syllogism (permConj _ _) p₁)
  let p₃ : Γ ⊢ B ⟹ ∼A ⟹ B := t23 _ _
  r49 p₂ p₃

theorem t40a (A B : Formula) : Γ ⊢ ∼(A ⋁ B) ⟹ (∼A ⋀ ∼B) :=
  let p₃ : Γ ⊢ A ⟹ ∼∼ (A ⋁ B) := syllogism (weakDisj A B) (t24 (A ⋁ B))
  let p₄ : Γ ⊢ ∼(A ⋁ B) ⋀ A ⟹ falsum := syllogism (permConj ∼(A ⋁ B) A) (importation p₃)
  let p₁ : Γ ⊢ ∼(A ⋁ B) ⟹ ∼A := exportation p₄

  let p₅ : Γ ⊢ B ⟹ ∼∼ (A ⋁ B) := syllogism (t20 A B) (t24 (A ⋁ B))
  let p₆ : Γ ⊢ ∼(A ⋁ B) ⋀ B ⟹ falsum := syllogism (permConj ∼(A ⋁ B) B) (importation p₅)
  let p₂ : Γ ⊢ ∼(A ⋁ B) ⟹ ∼B := exportation p₆

  r45 p₁ p₂

theorem t40b (A B : Formula) : Γ ⊢ (∼A ⋀ ∼B) ⟹ ∼(A ⋁ B) :=
  let p₁ : Γ ⊢ A ⟹ ∼A ⟹ ∼∼B := exportation (syllogism (permConj _ _) (t18 _ _))
  let p₂ : Γ ⊢ B ⟹ ∼A ⟹ ∼∼B := exportation (syllogism (permConj _ _) (importation (r44 (t24 _))))
  let p₃ : Γ ⊢ A ⋁ B ⟹ ∼A ⟹ ∼∼B := r49 p₁ p₂
  let p₄ : Γ ⊢ (∼A ⟹ ∼∼B) ⟹ ∼(∼A ⋀ ∼B) := t33b _ _
  let p₅ : Γ ⊢ A ⋁ B ⟹ ∼(∼A ⋀ ∼B) := syllogism p₃ p₄
  exportation (syllogism (permConj _ _) (importation p₅))