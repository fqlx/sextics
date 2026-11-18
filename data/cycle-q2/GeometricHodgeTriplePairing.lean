import Proposal.GeometricCartierDerivedClass

/-!
# Evaluation of three local sections

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

namespace CycleQ2HodgeTripleTangentCech

open CategoryTheory TopologicalSpace CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso

variable {X : TopCat.{0}}

/-- A sheafwise trilinear pairing, as supplied by evaluation of a three-form on three tangent fields. -/
structure Pairing (F G : AbSheaf X) where
  eval (W : Opens X) : Sections F W →+ Sections F W →+ Sections F W →+ Sections G W
  natural {W V : Opens X} (h : W ≤ V) (a b c : Sections F V) :
    res G h (eval V a b c) = eval W (res F h a) (res F h b) (res F h c)

end CycleQ2HodgeTripleTangentCech
