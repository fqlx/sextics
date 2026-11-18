import Proposal.GeometricLiteralMovingResidueCoordinates
import Proposal.GeometricLiteralMovingResidueBasis
import Proposal.GeometricLiteralMovingResidueAdjunction

/-!
# The row Jacobian opens and the complement of the moving curve

An affine refinement of the actual pivot and augmented-Jacobian opens covers
the surface once the matching pivot/minor condition holds on its curve.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralMovingResidueCoordinateBasis
open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2LiteralMovingResidueCoordinates CycleQ2LiteralMovingResidueBasis
  CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionInvertible
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionSheafCurveBinding
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricSurfaceAdjunction
open CycleQ2LiteralMovingResidueAdjunction.AffineFrame (Curve)

variable (t : Fin 3 → ℂ)

/-- Every point of the curve admits a row Jacobian patch for the same pivot. -/
def RowCover : Prop :=
  ∀ x : Curve t, ∃ (i : Fin 3) (p : Fin 3 × Fin 3) (s : SurfacePoly),
    (curveToSurface t) x ∈ pivotOpen i p ∧ (curveToSurface t) x ∈ rowOpen t i p.1 s

def Adapted (W : FramedAffine) : Prop :=
  (curveToSurface t) ⁻¹ᵁ W.carrier = ⊥ ∨ ∃ s : SurfacePoly, W.carrier ≤ rowOpen t W.frame.chart W.frame.pivot.1 s

/-- The local equation is a differential coordinate near the curve. In its
complement the ideal equals the entire structure sheaf. -/
theorem isBasis_adapted (hc : RowCover t) :
    Opens.IsBasis (Set.range (fun W : {W : FramedAffine // Adapted t W} => W.val.carrier)) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro U y hy
  by_cases hym : y ∈ Set.range (curveToSurface t)
  · obtain ⟨x,rfl⟩ := hym
    obtain ⟨i,p,s,hp,hs⟩ := hc x
    obtain ⟨V,hV,hx,hsub⟩ := Opens.isBasis_iff_nbhd.mp Surface.isBasis_affineOpens
      (show (curveToSurface t) x ∈ U ⊓ pivotOpen i p ⊓ rowOpen t i p.1 s from ⟨⟨hy,hp⟩,hs⟩)
    let A : FramedAffine := ⟨V,hV,(pivotFrameData i p).restrict ((hsub.trans inf_le_left).trans inf_le_right)⟩
    have ha : Adapted t A := Or.inr ⟨s,hsub.trans inf_le_right⟩
    exact ⟨V,⟨⟨A,ha⟩,rfl⟩,hx,(hsub.trans inf_le_left).trans inf_le_left⟩
  · let C := closedImageComplement (curveToSurface t)
    obtain ⟨V,⟨A,rfl⟩,hx,hsub⟩ := Opens.isBasis_iff_nbhd.mp isBasis_framedAffine
      (show y ∈ U ⊓ C from ⟨hy,hym⟩)
    have he : (curveToSurface t) ⁻¹ᵁ A.carrier = ⊥ := by
      apply le_antisymm _ bot_le
      exact (show (curveToSurface t) ⁻¹ᵁ A.carrier ≤ (curveToSurface t) ⁻¹ᵁ C from
        fun _ h => hsub.trans inf_le_right h).trans (preimage_closedImageComplement _).le
    exact ⟨A.carrier,⟨⟨A,Or.inl he⟩,rfl⟩,hx,hsub.trans inf_le_left⟩

end CycleQ2LiteralMovingResidueCoordinateBasis
end

#print axioms CycleQ2LiteralMovingResidueCoordinateBasis.isBasis_adapted
