

import ProofMining.FiniteType

-- inductive EHATerms (ρ: FiniteType) where
--   | const : EHATerms ρ
--   | var : EHATerms ρ
--   | app : {τ : FiniteType} → EHATerms (τ ↣ ρ) → EHATerms τ → EHATerms ρ


inductive EHATerms: FiniteType → Type where
  | const : {ρ: FiniteType} → EHATerms ρ
  | var : {ρ: FiniteType} → EHATerms ρ
  | app : {ρ: FiniteType} → {τ : FiniteType} → EHATerms (τ ↣ ρ) → EHATerms τ → EHATerms ρ


variable (ρ : FiniteType) (τ : FiniteType)

#check EHATerms ρ
#check EHATerms.const
#check EHATerms.var
#check EHATerms (τ ↣ ρ)
#check EHATerms.app