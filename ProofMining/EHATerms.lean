

import ProofMining.FiniteType

inductive EHATerms : FiniteType → Type where
  | const : EHATerms ρ
  | var : EHATerms ρ
  | app : (τ : FiniteType) → EHATerms (τ ↣ ρ) → EHATerms τ → EHATerms ρ