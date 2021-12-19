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
| recursorOne: FiniteType → Term
deriving DecidableEq, Inhabited

namespace Term

instance : Coe Nat Term := ⟨var⟩

infixl:80 " # " => app
notation "K" => kcomb
notation "S" => scomb
notation "R" => recursorOne

-- raise all variables above `cutoff` by `place` indices
def shift (place : Nat) (cutoff : Nat := 0) : Term → Term :=
fun term => match term with 
| var i => if i < cutoff then var i else var $ i + place
| app t u => app (t.shift place cutoff) (u.shift place cutoff) 
| zero => zero 
| successor => successor 
| kcomb ρ σ => kcomb ρ σ
| scomb ρ σ τ => scomb ρ σ τ
| recursorOne ρ => recursorOne ρ


/-
  `subst t i s` is the substitution of the occurrences of `i` by the term `s` in the term `t`
  A good notation could be something like t[s // i], TO FIND A GOOD NOTATION
-/
def subst : Term → Nat → Term → Term
| var j, i, s => if i = j then s else j
| app t u, i, s => app (t.subst i s) (u.subst i s)
| zero, _, _ => zero 
| successor, _, _ => successor 
| kcomb ρ σ, _, _ => kcomb ρ σ
| scomb ρ σ τ, _, _ => scomb ρ σ τ
| recursorOne ρ, _, _ => recursorOne ρ

def finiteTypeExpanderForRecursor (ρ : FiniteType) (ρ₁ : FiniteType) : FiniteType → FiniteType
| τ ↣ δ => (ρ ↣ 0 ↣ τ) ↣ finiteTypeExpanderForRecursor ρ ρ₁ δ
| 0 => ρ₁
| void => void

def recursorOneExpend (ρ : FiniteType) : FiniteType := 
match ρ with
  | τ ↣ δ => 0 ↣ ρ ↣ finiteTypeExpanderForRecursor ρ τ ρ
  | 0 => sorry
  | void => void

/-
  `WellTyped env t σ` means that t has type σ in the environment `env`
-/
inductive WellTyped (env : Environment) : Term → FiniteType → Prop 
| var (i σ) : env.nth i = some σ → WellTyped env (var i) σ 
| app (t u) (ρ τ) : WellTyped env t (ρ ↣ τ) → WellTyped env u ρ → WellTyped env (app t u) τ
| zero : WellTyped env zero 0
| successor : WellTyped env successor 1
| kcomb (ρ σ) : WellTyped env (kcomb ρ σ) (ρ ↣ σ ↣ ρ)
| scomb (ρ σ τ) : WellTyped env (scomb ρ σ τ) ((ρ ↣ σ ↣ τ) ↣ (ρ ↣ σ) ↣ ρ ↣ τ)
| recursorOne ρ : WellTyped env (recursorOne ρ) (recursorOneExpend ρ)

notation env " ⊢ " t " : " ρ:max => WellTyped env t ρ


/-
  Take a `term : Term` and an `env : Environment` and returns `some ρ` if `term` is well typed with `ρ` in `env`
  and `none` if `term` is ill-typed.
-/

-- def poorEq (ρ₀ : FiniteType) (ρ₁ : FiniteType) : Bool :=
--   match ρ₀ with
--     | FiniteType.zero => 
--       match ρ₁ with
--         | FiniteType.zero => true
--         | FiniteType.application _ _ => false
--     | FiniteType.application σ₀ τ₀ =>
--       match ρ₁ with
--         | FiniteType.zero => false
--         | FiniteType.application σ₁ τ₁ => ((poorEq σ₀ σ₁) && (poorEq τ₀ τ₁))

-- def goodEq : FiniteType → FiniteType → Bool 
-- | FiniteType.zero, FiniteType.zero => true 
-- | (ρ ↣ τ), (σ ↣ δ) => goodEq ρ σ && goodEq τ δ
-- | _, _ => false

@[simp]
def inferTypeAppAux : Option FiniteType → Option FiniteType → Option FiniteType 
| ρ ↣ τ, σ => if ρ = σ then some τ else none 
| _, _ => none

def inferType : Environment → Term → Option FiniteType
  | env, var x => List.nth env x
  | env, app x y => inferTypeAppAux (inferType env x) (inferType env y)
    
    -- WRONG SOLUTION
    -- match ρ₁ with
    --   | none => none
    --   | some σ =>
    --     match σ with
    --       | FiniteType.zero => none
    --       | FiniteType.application ρ₀ τ =>
    --         match ρ with
    --           | none => none
    --           | some ρ₂ => cond (ρ₀ = ρ₂) (some τ) none
  | env, zero => some (FiniteType.zero)
  | env, successor => some (FiniteType.zero ↣ FiniteType.zero)
  | env, kcomb ρ σ => some (ρ ↣ σ ↣ ρ)
  | env, scomb ρ σ τ => some ((ρ ↣ σ ↣ τ) ↣ (ρ ↣ σ) ↣ ρ ↣ τ) 
  | env, recursorOne ρ => some $ recursorOneExpend ρ
/-
  Sanity check for the above definitions. Show they define the same thing.
-/
theorem infer_type_iff_well_typed (env : Environment) (t : Term) (σ : FiniteType) : 
  WellTyped env t σ ↔ inferType env t = some σ := by
  apply Iff.intro
  . intros wt
    induction wt with
    | app _ _ _ _ _ _ h₁ h₂ => 
      simp [inferType, h₂, h₁]
    | var i _ h => 
      simp only [inferType]
      exact h
    | _ => simp only [inferType]
  . sorry


@[simp]
def isWellTyped (env : Environment) (t : Term) := Option.isSome $ inferType env t


/-
  A term can only have one type
-/

theorem unique_typing : WellTyped e t ρ → WellTyped e t σ → ρ = σ := by 
  intros wtρ wtσ 
  rw [infer_type_iff_well_typed] at wtρ wtσ 
  have : some ρ = some σ := Eq.trans wtρ.symm wtσ
  cases this
  rfl

/-
  Substitution preserves typing
-/


theorem subst_well_typed {env} {t s} {ρ σ} {i} : 
  WellTyped env t ρ → env.nth i = some σ → WellTyped env s σ → WellTyped env (t.subst i s) ρ := by 
  intros wtt wti wts 
  induction t generalizing ρ with 
  | var j => 
    byCases h : i = j 
    . rw [h] at wti ⊢
      cases wtt 
      have : some σ = some ρ := Eq.trans wti.symm (by assumption) --this is ridiculous. How do I anonymously name the hypotheses resulting from cases?!?!?!
      cases this
      simp [*, subst]
    . simp [*, subst]
  | app u v ihu ihv => 
    cases wtt with 
    | app _ _ τ _ wtu wtv =>
    exact WellTyped.app _ _ _ _ (ihu wtu) (ihv wtv) 
  | _ => 
    simp [*, subst]
#check @subst_well_typed

/-
  If a term has a type in an environment, then it has that same type in any larger environment
-/

theorem weakening {t} : WellTyped e₁ t ρ → List.Embedding e₁ e₂ → WellTyped e₂ t ρ := by 
  intros wt₁ wt₂
  induction t generalizing ρ with 
  | var j => 
    TODO_ALEX
  | app u v ihu ihv => 
    cases wt₁ with | app _ _ τ _ wtu wtv => 
    exact WellTyped.app _ _ _ _ (ihu wtu) (ihv wtv)
  | _ => cases wt₁; constructor

def idcomb (ρ : FiniteType) : Term := S ρ (0 ↣ ρ) ρ # K ρ (0 ↣ ρ) # K ρ 0
notation "I" => idcomb



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

