import ProofMining.Term 
import ProofMining.TermPrettyPrinter

open Term




def I (ρ : FiniteType) : Term := S ρ (0 ↣ ρ) ρ # K ρ (0 ↣ ρ) # K ρ 0

set_option print_types false

#reduce I

-- def K₂ (ρ τ : FiniteType) : Term := K (τ ↣ τ) ρ # I τ

-- variable (ρ τ : FiniteType)

-- example : inferType [] (K₂ ρ τ) = (ρ ↣ τ ↣ τ) := by 
--   simp [inferType]

def hasFV (t : Term) (i : Nat) : Bool := match t with 
| var j => i == j 
| app u v => hasFV u i || hasFV v i
| _ => false

def lambda (env : Environment) (src : FiniteType) (t : Term) : Term := 
  if h : !hasFV t 0 
    then K (inferType env t).get!! src # t.downShift 1
    else match t with 
    | var 0 => I src 
    | var (i + 1) => K (inferType env (i + 1 : Nat)).get!! src # (i + 1 : Nat)
    | app u v => app (lambda env src u) (lambda env src v)
    -- ???the following cases whould be simply defined by exfalso, but how do we write that???
    | kcomb ρ τ => K (inferType env $ K ρ τ).get!! src # (K ρ τ)
    | scomb ρ τ σ => K (inferType env $ S ρ τ σ).get!! src # (S ρ τ σ)
    | zero => K (inferType env zero).get!! src # zero 
    | successor => K (inferType env successor).get!! src # successor 
    | recursorOne ρ => K (inferType env $ R ρ).get!! src # (R ρ)
  

def l : Term := lambda [𝕆, 𝕆] 𝕆 (lambda [𝕆, 𝕆] 𝕆 (var 1))
def l' : Term := lambda [] 𝕆 (I 𝕆)
#reduce l


theorem beta_reduction (env : Environment) : (lambda env ρ t) # s = t.subst 0 s := sorry


