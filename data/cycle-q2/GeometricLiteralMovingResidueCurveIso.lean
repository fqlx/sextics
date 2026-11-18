import Proposal.GeometricLiteralMovingResidueCurve

/-!
# A local criterion for moving-curve adjunction

On any basis of framed affine opens, bijectivity of the native curve-ring maps
detects invertibility of the global residue morphism.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralMovingResidueCurveIso

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricAffineOverlap CycleQ2GeometricSectionDifferentials
  CycleQ2SeedSectionAffineInjective CycleQ2SeedSectionSheafCurveBinding
  CycleQ2LiteralMovingResidueBasis CycleQ2LiteralMovingResidueAdjunction
  CycleQ2LiteralMovingResidueCurve
open CycleQ2LiteralMovingResidueAdjunction.AffineFrame

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

/-- The component of the global morphism is bijective on a framed affine open
exactly when its map on ordinary affine curve differentials is bijective. -/
theorem curveResidue_app_bijective_iff (W : FramedAffine) :
    Function.Bijective ((curveResidue t ht).hom.app (op W.carrier)) ↔
      Function.Bijective (curveAdjunction W.affine t ht W.frame) := by
  let f := (curveResidue t ht).hom.app (op W.carrier)
  let g := toSheaf (Curve t).sheaf (curveCoefficient t) ((curveToSurface t) ⁻¹ᵁ W.carrier)
  have hg : Function.Bijective g := CycleQ2AffineOpenOrdinaryDifferentials.toSheaf_bijective_of_isAffineOpen
    (curveCoefficient t) _ (W.affine.preimage (curveToSurface t))
  have e : (fun x => f (g x)) = curveAdjunction W.affine t ht W.frame := by
    funext x
    exact curveResidue_basis t ht W x
  rw [← e]
  exact (Function.Bijective.of_comp_iff f hg).symm

/-- A smooth-coordinate refinement may be used instead of testing every
affine pivot, and the conclusion is an isomorphism on the entire surface. -/
theorem curveResidue_isIso_of_basis {ι : Type*} (B : ι → FramedAffine)
    (hB : Opens.IsBasis (Set.range (fun i => (B i).carrier)))
    (h : ∀ i, Function.Bijective (curveAdjunction (B i).affine t ht (B i).frame)) :
    IsIso (curveResidue t ht) := by
  apply TopCat.Sheaf.isIso_iff_isIso_basis hB
  intro i
  exact (ConcreteCategory.isIso_iff_bijective _).mpr ((curveResidue_app_bijective_iff t ht (B i)).mpr (h i))

end CycleQ2LiteralMovingResidueCurveIso
end

#print axioms CycleQ2LiteralMovingResidueCurveIso.curveResidue_isIso_of_basis
