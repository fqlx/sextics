import Proposal.ScratchWeightedTupleCycle
import Proposal.ScratchWeightedProperPrimitive

/-! A native Čech cocycle with only the three residue components gives
a derived degree-three class on the proper sextic. Its image at the chosen
generic point is the original primitive obstruction. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open CategoryTheory AlgebraicGeometry
open CycleQ2.Cech CycleQ2CechDeRhamTotalThree CycleQ2WeightedNativeCech
open CycleQ2GeometricHodgeThreefold CycleQ2WeightedResidueAtlas
  CycleQ2WeightedGenericPointMap CycleQ2WeightedConeUniversal CycleQ2WeightedChosenResidue
open CycleQ2GenericSexticGradient
namespace CycleQ2WeightedLiftClass

theorem components {B : Double} (z : Cycles B) (ht : z.1.2.2.2 = 0) :
    B.v 0 3 z.1.1 = 0 ∧ B.h 0 3 z.1.1 = -(B.v 1 2 (-z.1.2.1)) ∧
      B.h 1 2 (-z.1.2.1) = B.v 2 1 z.1.2.2.1 ∧ B.h 2 1 z.1.2.2.1 = 0 := by
  have hz : d3 B z.1 = 0 := z.2
  have h₁ := congrArg (fun s : Four B => s.2.1) hz
  have h₂ := congrArg (fun s : Four B => s.2.2.1) hz
  have h₃ := congrArg (fun s : Four B => s.2.2.2.1) hz
  change B.h 0 3 z.1.1 - B.v 1 2 z.1.2.1 = 0 at h₁
  change B.h 1 2 z.1.2.1 + B.v 2 1 z.1.2.2.1 = 0 at h₂
  change B.h 2 1 z.1.2.2.1 - B.v 3 0 z.1.2.2.2 = 0 at h₃
  refine ⟨congrArg Prod.fst hz,?_,?_,?_⟩
  · simpa using sub_eq_zero.mp h₁
  · rw [map_neg,eq_neg_of_add_eq_zero_left h₂,neg_neg]
  · simpa [ht] using h₃

variable {k : Type} [CommRing k] (φ : CoeffRing →+* k)
  [HasDerivedCategory (CycleQ2InjectiveCech.AbSheaf (threefold φ : TopCat))]

abbrev proper (z : Cycles (double φ)) (ht : z.1.2.2.2 = 0) (hg : IsUnit (φ goodParameter)) :=
  WeightedSheaf.properClass φ z.1.1 (-z.1.2.1) z.1.2.2.1 (components z ht).1
    (components z ht).2.1 (components z ht).2.2.1 (components z ht).2.2.2 hg

section Universal
variable [HasDerivedCategory (CycleQ2InjectiveCech.AbSheaf (threefold coefficients : TopCat))]
theorem primitive_of_vanishing (z : Cycles (double coefficients)) (ht : z.1.2.2.2 = 0)
    (hv : vertex (U coefficients) (Native.P (toBase coefficients) 3) chosen z.1.1 = form)
    (hz : proper coefficients z ht goodParameter_unit = 0) :
    CycleQ2UniversalWeightedTransfer.UniversalWeightedPrimitiveExists :=
  CycleQ2WeightedProperPrimitive.primitive_of_proper_zero z.1.1 (-z.1.2.1) z.1.2.2.1
    (components z ht).1 (components z ht).2.1 (components z ht).2.2.1
    (components z ht).2.2.2 hv hz
end Universal

end CycleQ2WeightedLiftClass
end
#print axioms CycleQ2WeightedLiftClass.primitive_of_vanishing
