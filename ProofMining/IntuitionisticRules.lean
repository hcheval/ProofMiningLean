-- Chapter 9.4 From "Articol rules"

import ProofMining.Proof
import ProofMining.Formula

open Formula (falsum)
namespace Proof

theorem r44 {A B : Formula} (h : Γ ⊢ A) : Γ ⊢ B ⟹ A :=
  let p₁ : Γ ⊢ A ⋀ B ⟹ A := weakConj' 
  let p₂ : Γ ⊢ A ⟹ (B ⟹ A) := exportation p₁ 
  mpon h p₂

theorem r45 {A B C : Formula} (h₁ : Γ ⊢ A ⟹ B) (h₂ : Γ ⊢ A ⟹ C) : Γ ⊢ A ⟹ B ⋀ C :=
  let p₁ : Γ ⊢ B ⋀ C ⟹ B ⋀ C := syllogism (permConj B C) (permConj C B)
  let p₂ : Γ ⊢ B ⟹ (C ⟹ B ⋀ C) := exportation p₁
  let p₃ : Γ ⊢ A ⟹ (C ⟹ B ⋀ C) := syllogism h₁ p₂
  let p₄ : Γ ⊢ A ⋀ C ⟹ B ⋀ C := importation p₃
  let p₅ : Γ ⊢ C ⋀ A ⟹ B ⋀ C := syllogism (permConj _ _) p₄
  let p₆ : Γ ⊢ C ⟹ (A ⟹ B ⋀ C) := exportation p₅
  let p₇ : Γ ⊢ A ⋀ A ⟹ B ⋀ C := importation (syllogism h₂ p₆)
  syllogism (contrConj _) p₇

theorem r46 {A B C : Formula} (h : Γ ⊢ A ⟹ B) : Γ ⊢ A ⋀ C ⟹ B ⋀ C :=
  let p₁ : Γ ⊢ C ⋀ A ⟹ B := importation (r44 h)
  let p₂ : Γ ⊢ A ⋀ C ⟹ B := syllogism (permConj _ _) p₁
  let p₃ : Γ ⊢ A ⋀ C ⟹ C := syllogism (permConj _ _) (weakConj _ _)
  r45 p₂ p₃

theorem r49 {A B C : Formula} (h₁ : Γ ⊢ A ⟹ C) (h₂ : Γ ⊢ B ⟹ C) : Γ ⊢ A ⋁ B ⟹ C :=
  let p₁ : Γ ⊢ A ⋁ B ⟹ A ⋁ C := expansion A h₂
  let p₂ : Γ ⊢ C ⋁ A ⟹ C ⋁ C := expansion C h₁
  let p₃ : Γ ⊢ A ⋁ C ⟹ C ⋁ C := syllogism (permDisj _ _) p₂
  let p₄ : Γ ⊢ A ⋁ C ⟹ C := syllogism p₃ (contrDisj C)
  syllogism p₁ p₄

theorem r50 {A B : Formula} (h₁ : Γ ⊢ A) (h₂ : Γ ⊢ B) : Γ ⊢ A ⋀ B :=
  let p₁ : Γ ⊢ A ⟹ (B ⟹ A ⋀ B) := exportation (syllogism (permConj A B) (permConj B A))
  let p₂ : Γ ⊢ B ⟹ A ⋀ B  := mpon h₁ p₁
  mpon h₂ p₂

theorem r42 {A : Formula} {ρ : FiniteType} (h₁ : Γ ⊢ A) : Γ ⊢ ∀∀ ρ A := 
  let p₁ : Γ ⊢ A ⟹ A := syllogism (contrConj _) (weakConj _ _)
  let p₂ : Γ ⊢ A ⟹ ∀∀ ρ A := universalRule ρ p₁
  mpon h₁ p₂
