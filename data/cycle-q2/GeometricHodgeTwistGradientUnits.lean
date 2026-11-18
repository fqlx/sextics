import Proposal.GeometricHodgeTwistGradientCover

/-!
# The chosen normalized derivative is a unit on each moving pivot chart

The degree-zero localization at xᵢ∂ᵢF localizes the xᵢ-chart at the
function ∂ᵢF/xᵢ⁵. The projective localization's section map carries its
unit to the genuine normalized derivative on every subopen.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeTwistGradientCover
open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold
open CycleQ2HodgeEulerSheaf (partialValue partial_mem)
open CycleQ2GeometricProjectiveCurve.Twisted (res)
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2HodgeTwistRatios (normalized normalized_restrict)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Fin 4)

theorem pivotOpen_affine : IsAffineOpen (pivotOpen φ i) := by
  apply Proj.isAffineOpen_basicOpen (grade φ) (product φ i.castSucc)
    (SetLike.mul_mem_graded (weightOne_mem_grade φ i) (partial_mem φ i.castSucc))
  omega

private abbrev PivotRing := Away (grade φ) (product φ i.castSucc)

private def toPivot : ChartRing φ i →+* PivotRing φ i :=
  awayMap (grade φ) (partial_mem φ i.castSucc) rfl

private abbrev frac := Away.isLocalizationElem (weightOne_mem_grade φ i) (partial_mem φ i.castSucc)

private theorem toPivot_unit : IsUnit (toPivot φ i (frac φ i)) := by
  letI := (toPivot φ i).toAlgebra
  letI : IsLocalization.Away (frac φ i) (PivotRing φ i) :=
    Away.isLocalization_mul (weightOne_mem_grade φ i) (partial_mem φ i.castSucc) rfl (by decide)
  exact IsLocalization.Away.algebraMap_isUnit (frac φ i)

private theorem section_frac :
    (Proj.awayToSection (grade φ) (product φ i.castSucc)) (toPivot φ i (frac φ i)) =
      normalized φ i (partialValue φ i.castSucc) (partial_mem φ i.castSucc) (pivotOpen φ i) (pivotOpen_le φ i) := by
  let p : ChartRing φ i := Away.mk (grade φ) (weightOne_mem_grade φ i) (6 - geometricWeight i.castSucc)
    (partialValue φ i.castSucc) (by simpa using partial_mem φ i.castSucc)
  have hp : frac φ i = p := by
    apply HomogeneousLocalization.val_injective
    simp only [frac, Away.isLocalizationElem, p, Away.val_mk, pow_one]
  rw [hp]
  have h := Proj.awayMap_awayToSection (grade φ) (partial_mem φ i.castSucc)
    (show product φ i.castSucc = coord φ i.castSucc * partialValue φ i.castSucc from rfl)
  exact congrArg (fun u : CommRingCat.of (ChartRing φ i) ⟶ Γ(threefold φ,pivotOpen φ i) => u.hom p) h

theorem normalized_partial_isUnit (V : (threefold φ).Opens) (hV : V ≤ pivotOpen φ i) :
    IsUnit (normalized φ i (partialValue φ i.castSucc) (partial_mem φ i.castSucc) V
      (hV.trans (pivotOpen_le φ i))) := by
  rw [← normalized_restrict φ i _ _ (pivotOpen_le φ i) hV, ← section_frac]
  exact ((toPivot_unit φ i).map (Proj.awayToSection (grade φ) (product φ i.castSucc)).hom).map
    (res (threefold φ).sheaf hV)

end CycleQ2HodgeTwistGradientCover
end
#print axioms CycleQ2HodgeTwistGradientCover.pivotOpen_affine
#print axioms CycleQ2HodgeTwistGradientCover.normalized_partial_isUnit
