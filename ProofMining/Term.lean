import ProofMining.FiniteType 
import ProofMining.Util

/-
  A typing environment provides types for free variables.
  `[ρ₀, ρ₁, ..., ρₙ] : Environment` means that the variable 0 has type ρ₀, 1 has type ρ₁ and so on.
-/
abbrev Environment := List FiniteType

/-
  Extrinsically typed terms.
  Probably the better choice
-/

inductive Term 
| var : Nat → Term  -- De Bruijn variables
| app : Term → Term → Term 
| zero : Term 
| successor : Term 
| kcomb : FiniteType → FiniteType → Term -- the K combinator, or Π in Kohlenbach's book
| scomb : FiniteType → FiniteType → FiniteType → Term -- the S combinator, or Σ in Kohlenbach's book

namespace Term

/-
  `wellTyped env t σ` means that t has type σ in the environment `env`
-/
inductive wellTyped (env : Environment) : Term → FiniteType → Prop 
| var (i σ) : env.nth i = some σ → wellTyped env (var i) σ 
| app (t u) (ρ τ) : wellTyped env t (ρ ↣ τ) → wellTyped env u ρ → wellTyped env (app t u) τ
| zero : wellTyped env zero 0
| successor : wellTyped env successor 1
| kcomb (ρ σ) : wellTyped env (kcomb ρ σ) (ρ ↣ σ ↣ ρ)
| scomb (ρ σ τ) : wellTyped env (scomb ρ σ τ) ((ρ ↣ σ ↣ τ) ↣ (ρ ↣ σ) ↣ ρ ↣ τ)


/-
  Take a `term : Term` and an `env : Environment` and returns `some ρ` if `term` is well typed with `ρ` in `env`
  and `none` if `term` is ill-typed.
-/
def inferType (env : Environment) (term : Term) : Option FiniteType
  | env, var x => List.nth env x
  | env, app x y => sorry
  | env, zero => List.nth env 0
  | env, successor => List.nth env 1
  | env, kcomb ρ σ => sorry
  | env, scomb ρ σ τ => sorry

/-
  Sanity check for the above definitions. Show they define the same thing.
-/
theorem infer_type_iff_well_typed (env : Environment) (t : Term) (σ : FiniteType) : 
  wellTyped env t σ ↔ inferType env t = some σ := sorry


/-
  Intrinsically typed terms.
  Closer to the "pen and paper" definition, but may cause trouble later on due to the type dependencies.
  Note that typing enviornments are still needed because of De Bruijn variables.
  With named variables we could have not needed environments.
-/

-- inductive Term (env : Environment) : FiniteType → Type 
-- | var {ρ : FiniteType} (i : Nat) : List.nth env i = some ρ → Term env ρ
-- | app {ρ σ : FiniteType} : Term env (ρ ↣ τ) → Term env ρ → Term env τ
-- | zero : Term env FiniteType.zero
-- | successor : Term env (FiniteType.zero ↣ FiniteType.zero)
-- | kcomb {ρ σ : FiniteType} : Term env (ρ ↣ σ ↣ ρ)
-- | scomb {ρ σ τ : FiniteType} : Term env $ (ρ ↣ σ ↣ τ) ↣ (ρ ↣ σ) ↣ ρ ↣ τ
