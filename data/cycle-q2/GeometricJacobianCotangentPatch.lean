import Proposal.GeometricExteriorLocalFrames

/-!
# Cotangent coordinates on a Jacobian patch

The first cotangent basis vector is the differential of the chosen
polynomial. The residue coordinate identifies the exterior square of
sections with sections of the canonical sheaf on every subopen of the patch.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2JacobianCotangentPatch

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
  CycleQ2GeometricSurfaceAdjunction CycleQ2GeometricAffineChartSections
  CycleQ2GeometricFunctionalDifferentials CycleQ2GeometricSurfaceExteriorSections
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricExteriorLocalFrames
  CycleQ2GeometricSheafKaehlerMap CycleQ2GeometricDifferentialSheaf

section AbstractPatch
variable {Y : Scheme.{0}} {U : Y.Opens} (f : Y ⟶ Spec (CommRingCat.of ℂ))
  (u : Fin 2 → SurfacePoly) (n₀ s₀ : SurfacePoly)
  (e : U.toScheme ≅ Spec (CommRingCat.of (AdjunctionPatch u n₀ s₀)))
  (hc : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ (AdjunctionPatch u n₀ s₀))))

/-- The first Jacobian cotangent coordinate is the universal differential of the chosen polynomial. -/
theorem firstBasis_D (V' : Over U) :
    (chartSectionBasis e f hc (localSurfaceKaehlerBasis u n₀ s₀) V') 0 =
      (universalDifferential Y.sheaf (schemeCoefficient f)).d
        (chartSection e V' (algebraMap SurfacePoly (AdjunctionPatch u n₀ s₀) n₀)) := by
  let b := localSurfaceKaehlerBasis u n₀ s₀
  refine (chartSectionBasis_apply e f hc b V' 0).trans
    ((chartRestrictedBasisSection_eq_sectionLift e f hc b V' 0).trans ?_)
  exact (congrArg (chartKaehlerSection e f hc V') (localSurfaceKaehlerBasis_apply u n₀ s₀ 0)).trans
    (sectionLift_D Y.sheaf (schemeCoefficient f) _ _ _ _ _ _)

private theorem bijective_of_coordinate {P Q S : Type*} (L : P → Q) (F : Q → S) (c : P → S)
    (hF : Function.Bijective F) (hc : Function.Bijective c) (h : ∀ x, F (L x) = c x) :
    Function.Bijective L := by
  apply (Function.Bijective.of_comp_iff' hF L).mp
  have e : F ∘ L = c := funext h
  rwa [e]

include hc in
/-- On every subopen of the Jacobian patch, the exterior square of sections maps
bijectively to the sections of the exterior-square sheaf. -/
theorem exterior_bijective {W' : Y.Opens} (hw : W' ≤ U) :
    Function.Bijective (exteriorSection Y.sheaf (differentialSheaf Y.sheaf (schemeCoefficient f)).val 2 W') := by
  let F := (chartResidueLocalFrame f u n₀ s₀ e hc).app W' hw
  let c := chartResidueCoordinate f u n₀ s₀ e hc (Over.mk (homOfLE hw))
  exact bijective_of_coordinate _ F c F.bijective c.bijective
    (chartResidueLocalFrame_exteriorSection f u n₀ s₀ e hc W' hw)

end AbstractPatch

end CycleQ2JacobianCotangentPatch
end

#print axioms CycleQ2JacobianCotangentPatch.firstBasis_D
#print axioms CycleQ2JacobianCotangentPatch.exterior_bijective
