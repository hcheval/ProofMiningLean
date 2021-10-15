/-
  The type of propositional formulas.
  We have no terms and no atomic formulas beyond faslumat the moment, as they are irrelevant for proving propositional logic results.
  We will add them later.
  The same remark applies to constructors corresponding to quantifiers.
-/

inductive Formula
| conjunction : Formula → Formula → Formula
| disjunction : Formula → Formula → Formula
| implication : Formula → Formula → Formula
| falsum : Formula


namespace Formula
/-
  Familiar notations.
  Note that ⋀ and ⋁ bind stronger than ⟹ and that ⟹ is right-associative.
-/
infixl:55 "⋀" => conjunction --input with \ bigvee 
infixl:55 "⋁" => disjunction --input with \ bigwedge
infixr:50 "⟹" => implication --input with \ ==>

