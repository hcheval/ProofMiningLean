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

theorem t18 (A B : Formula) : Γ ⊢ ((A ⟹ falsum) ⋀ A ⟹ B) :=
  let p₁ : Γ ⊢ (falsum ⟹ B) := exFalso _
  let p₂ : Γ ⊢ ((A ⟹ falsum) ⋀ A ⟹ falsum) := importation (t21 (A ⟹ falsum))
  syllogism p₂ p₁

theorem t22 (A B : Formula) : Γ ⊢ A ⟹ (B ⟹ (A ⋀ B)) :=
  let p₁ : Γ ⊢ (A ⋀ B) ⟹ (A ⋀ B) := t21 _
  exportation p₁

theorem t23 (A B : Formula) : Γ ⊢ A ⟹ (B ⟹ A) :=
  let p₁ : Γ ⊢ (A ⋀ B) ⟹ A := weakConj _ _
  exportation p₁

theorem t24 (A : Formula) : Γ ⊢ (A ⟹ ((A ⟹ falsum) ⟹ falsum)) :=
  let p₁ : Γ ⊢ (A ⋀ (A ⟹ falsum) ⟹ (A ⟹ falsum) ⋀ A) := permConj _ _
  let p₂ : Γ ⊢ (A ⋀ (A ⟹ falsum) ⟹ falsum) := syllogism p₁ (t18 A falsum)
  exportation p₂

theorem t25 (A : Formula) : Γ ⊢ ((A ⋁ (A ⟹ falsum)) ⟹ falsum) ⟹ falsum := 
  sorry

theorem t26a (A : Formula) : Γ ⊢ (A ⟹ falsum) ⟹ (((A ⟹ falsum) ⟹ falsum) ⟹ falsum) :=
  t24 (A ⟹ falsum)

theorem t26b (A : Formula) : Γ ⊢ (((A ⟹ falsum) ⟹ falsum) ⟹ falsum) ⟹ (A ⟹ falsum) :=
  sorry

theorem t27a (A B : Formula) : Γ ⊢ (((A ⟹ B) ⟹ falsum) ⟹ falsum) ⟹ (A ⟹ ((B ⟹ falsum) ⟹ falsum)) :=
  sorry

theorem t27b (A B : Formula) : Γ ⊢ (A ⟹ ((B ⟹ falsum) ⟹ falsum)) ⟹ (((A ⟹ B) ⟹ falsum) ⟹ falsum) :=
  sorry

theorem t28a (A B : Formula) : Γ ⊢ (((A ⟹ B) ⟹ falsum) ⟹ falsum) ⟹ (((A ⟹ falsum) ⟹ falsum) ⟹ ((B ⟹ falsum) ⟹ falsum)) :=
  sorry

theorem t28b (A B : Formula) : Γ ⊢ (((A ⟹ falsum) ⟹ falsum) ⟹ ((B ⟹ falsum) ⟹ falsum)) ⟹ (((A ⟹ B) ⟹ falsum) ⟹ falsum) :=
  sorry

theorem t29a (A B : Formula) : Γ ⊢ (A ⟹ (B ⟹ falsum)) ⟹ (((A ⟹ falsum) ⟹ falsum) ⟹ (B ⟹ falsum)) :=
  let p₁ : Γ ⊢ (A ⟹ (B ⟹ falsum)) ⟹ (((A ⟹ falsum) ⟹ falsum) ⟹ (((B ⟹ falsum) ⟹ falsum) ⟹ falsum)) := syllogism (t24 _) (t28a _ _)
  let p₂ : Γ ⊢ (((A ⟹ falsum) ⟹ falsum) ⟹ (((B ⟹ falsum) ⟹ falsum) ⟹ falsum)) ⟹ (((A ⟹ falsum) ⟹ falsum) ⟹ (B ⟹ falsum)) := exportation (syllogism (importation (t21 _)) (t26b _))
  syllogism p₁ p₂

theorem t29b (A B : Formula) : Γ ⊢ (((A ⟹ falsum) ⟹ falsum) ⟹ (B ⟹ falsum)) ⟹ (A ⟹ (B ⟹ falsum)) :=
  sorry

theorem t30a (A B : Formula) : Γ ⊢ (((A ⋀ B) ⟹ falsum) ⟹ falsum) ⟹ (((A ⟹ falsum) ⟹ falsum) ⋀ ((B ⟹ falsum) ⟹ falsum)) :=
  sorry

theorem t30b (A B : Formula) : Γ ⊢ (((A ⟹ falsum) ⟹ falsum) ⋀ ((B ⟹ falsum) ⟹ falsum)) ⟹ (((A ⋀ B) ⟹ falsum) ⟹ falsum) :=
  sorry

theorem t31 (A B : Formula) : Γ ⊢ (((A ⋁ B) ⟹ falsum) ⟹ falsum) ⟹ ((A ⟹ falsum) ⟹ falsum) ⟹ ((B ⟹ falsum) ⟹ falsum) :=
  sorry

theorem t32a (A B : Formula) : Γ ⊢ (((A ⋁ B) ⟹ falsum) ⟹ falsum) ⟹ (((A ⟹ falsum) ⋀ (B ⟹ falsum)) ⟹ falsum) :=
  sorry

theorem t32b (A B : Formula) : Γ ⊢ (((A ⟹ falsum) ⋀ (B ⟹ falsum)) ⟹ falsum) ⟹ (((A ⋁ B) ⟹ falsum) ⟹ falsum) :=
  sorry

theorem t33a (A B : Formula) : Γ ⊢ ((A ⋀ B) ⟹ falsum) ⟹ A ⟹ (B ⟹ falsum) :=
  let p₁ : Γ ⊢ A ⟹ B ⟹ ((A ⋀ B) ⟹ falsum)  ⟹ falsum := exportation (t24 _)
  sorry

theorem t33b (A B : Formula) : Γ ⊢ (A ⟹ (B ⟹ falsum)) ⟹ ((A ⋀ B) ⟹ falsum) :=
  sorry

theorem t35 (A B : Formula) : Γ ⊢ A ⋁ B ⟹ (A ⟹ falsum) ⟹ B :=
  let p₁ : Γ ⊢ (A ⟹ falsum) ⋀ A ⟹ B := t18 _ _
  let p₂ : Γ ⊢ A ⟹ (A ⟹ falsum) ⟹ B := exportation (syllogism (permConj _ _) p₁)
  let p₃ : Γ ⊢ B ⟹ (A ⟹ falsum) ⟹ B := t23 _ _
  r49 p₂ p₃

theorem t40a (A B : Formula) : Γ ⊢ ((A ⋁ B) ⟹ falsum) ⟹ ((A ⟹ falsum) ⋀ (B ⟹ falsum)) :=
  let p₃ : Γ ⊢ A ⟹ (((A ⋁ B) ⟹ falsum) ⟹ falsum) := syllogism (weakDisj A B) (t24 (A ⋁ B))
  let p₄ : Γ ⊢ ((A ⋁ B) ⟹ falsum) ⋀ A ⟹ falsum := syllogism (permConj ((A ⋁ B) ⟹ falsum) A) (importation p₃)
  let p₁ : Γ ⊢ ((A ⋁ B) ⟹ falsum) ⟹ (A ⟹ falsum) := exportation p₄

  let p₅ : Γ ⊢ B ⟹ (((A ⋁ B) ⟹ falsum) ⟹ falsum) := syllogism (t20 A B) (t24 (A ⋁ B))
  let p₆ : Γ ⊢ ((A ⋁ B) ⟹ falsum) ⋀ B ⟹ falsum := syllogism (permConj ((A ⋁ B) ⟹ falsum) B) (importation p₅)
  let p₂ : Γ ⊢ ((A ⋁ B) ⟹ falsum) ⟹ (B ⟹ falsum) := exportation p₆

  r45 p₁ p₂

theorem t40b (A B : Formula) : Γ ⊢ ((A ⟹ falsum) ⋀ (B ⟹ falsum)) ⟹ ((A ⋁ B) ⟹ falsum) :=
  let p₁ : Γ ⊢ A ⟹ (A ⟹ falsum) ⟹ ((B ⟹ falsum) ⟹ falsum) := exportation (syllogism (permConj _ _) (t18 _ _))
  let p₂ : Γ ⊢ B ⟹ (A ⟹ falsum) ⟹ ((B ⟹ falsum) ⟹ falsum) := exportation (syllogism (permConj _ _) (importation (r44 (t24 _))))
  let p₃ : Γ ⊢ A ⋁ B ⟹ (A ⟹ falsum) ⟹ ((B ⟹ falsum) ⟹ falsum) := r49 p₁ p₂
  let p₄ : Γ ⊢ ((A ⟹ falsum) ⟹ ((B ⟹ falsum) ⟹ falsum)) ⟹ ((A ⟹ falsum) ⋀ (B ⟹ falsum) ⟹ falsum) := t33b _ _
  let p₅ : Γ ⊢ A ⋁ B ⟹ ((A ⟹ falsum) ⋀ (B ⟹ falsum) ⟹ falsum) := syllogism p₃ p₄
  exportation (syllogism (permConj _ _) (importation p₅))