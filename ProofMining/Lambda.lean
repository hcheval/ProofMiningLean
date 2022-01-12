import ProofMining.Term 
import ProofMining.TermPrettyPrinter

open Term

set_option print_types false


-- def K₂ (ρ τ : FiniteType) : Term := K (τ ↣ τ) ρ # I τ

-- variable (ρ τ : FiniteType)

-- example : inferType [] (K₂ ρ τ) = (ρ ↣ τ ↣ τ) := by 
--   simp [inferType]

def hasFV (t : Term) (i : Nat) : Bool := match t with 
| var j => i == j 
| app u v => hasFV u i || hasFV v i
| _ => false

open FiniteType (void)

def lambda (env : Environment) (src : FiniteType) (t : Term) : Term := 
match t with 
| var 0 => I src
| var (i + 1) => K void void # i
| app u v => S void void void # (lambda env src u) # (lambda env src v)
| K ρ τ => K void void # K ρ τ
| S ρ τ δ => K void void # S ρ τ δ 
| zero => K void void # zero 
| successor => K void void # successor  
| R ρ => K void void # R ρ
  

def l : Term := lambda [𝕆, 𝕆] 𝕆 (lambda [𝕆, 𝕆] 𝕆 (var 1))
def l' : Term := lambda [] 𝕆 (I 𝕆)
#reduce l

def K₂ (ρ τ) := lambda [] ρ $ lambda [] τ 0

def x : Term := K₂ 𝕆 𝕆 # Term.zero # Term.successor 

def proj₁₃ (ρ τ σ : FiniteType) : Term := lambda [] ρ (lambda [] τ (lambda [] σ 1))

-- #reduce proj₁₃

#reduce iterate reduceOneStep 11 $ proj₁₃ 𝕆 𝕆 𝕆 # (Term.zero) # (Term.successor) # Term.successor

#reduce iterate reduceOneStep 3 x

-- theorem beta_reduction (env : Environment) : (lambda env ρ t) # s = t.subst 0 s := sorry


