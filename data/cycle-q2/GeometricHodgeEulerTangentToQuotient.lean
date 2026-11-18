import Proposal.GeometricHodgeEulerQuotientFrames
import Proposal.GeometricHodgeEulerTangentJacobian

/-! On each native weight-one open, differentiate the five normalized
coordinates and use these values as an ambient tangent vector. The
projective Euler quotient removes its dependence on the chosen pivot.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerTangentToQuotient

open CategoryTheory Limits Opposite AlgebraicGeometry
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2GeometricHodgeThreefold (threefold coordinateOpen coord coord_mem_grade toBase)
open CycleQ2HodgeTwistRatios (normalized normalized_change normalized_restrict U)
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal
open CycleQ2HodgeEulerSheaf CycleQ2HodgeThreefoldTwist
open CycleQ2HodgeEulerQuotientSections (rawCoordinate rawCoordinate_restrict)
open CycleQ2HodgeEulerQuotientFrames (gradients euler ambientEquiv)
open CycleQ2HodgeEulerTangentSheaf CycleQ2HodgeEulerTangentValues CycleQ2HodgeEulerTangentCoordinates
open CycleQ2SeedSectionSheafLocal (moduleRes moduleRes_app)
open CycleQ2HodgeEuler (pairing pairing_apply chartMap F coordinate conePartial)

variable (φ : CoeffRing →+* ℂ) (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)

def lift : Γ(tangent (toBase φ),V) →ₗ[Γ(threefold φ,V)] Γ(rawTangent φ,V) :=
  (ambientEquiv φ i V hi).symm.toLinearMap ∘ₗ (valuesLinear φ i V hi).codRestrict _ (tangent_equation φ i V hi)

theorem lift_coordinate (s : Γ(tangent (toBase φ),V)) (j : Fin 5) :
    rawCoordinate φ i V hi j (lift φ i V hi s) = values φ i V hi s j := by
  exact congrFun (congrArg Subtype.val ((ambientEquiv φ i V hi).apply_symm_apply
    (⟨values φ i V hi s, tangent_equation φ i V hi s⟩ : (pairing (gradients φ i V hi)).ker))) j

def toQuotient : Γ(tangent (toBase φ),V) →ₗ[Γ(threefold φ,V)] Γ(tangentQuotient φ,V) :=
  ((cokernel.π (radialTangent φ)).val.app (op V)).hom ∘ₗ lift φ i V hi

theorem frame_toQuotient (s : Γ(tangent (toBase φ),V)) (j : Fin 4) :
    (CycleQ2HodgeEulerQuotientFrames.frame φ i V hi (toQuotient φ i V hi s)).val j =
      values φ i V hi s (i.castSucc.succAbove j) := by
  rw [show toQuotient φ i V hi s = (cokernel.π (radialTangent φ)).app V (lift φ i V hi s) from rfl,
    CycleQ2HodgeEulerQuotientFrames.frame_project]
  change rawCoordinate φ i V hi _ (lift φ i V hi s) - rawCoordinate φ i V hi i.castSucc (lift φ i V hi s) *
    euler φ i V hi _ = _
  rw [lift_coordinate, lift_coordinate, pivot_zero, zero_mul, sub_zero]

theorem lift_restrict {W : (threefold φ).Opens} (hW : W ≤ V) (s : Γ(tangent (toBase φ),V)) :
    lift φ i W (hW.trans hi) (moduleRes _ hW s) = moduleRes _ hW (lift φ i V hi s) := by
  apply (ambientEquiv φ i W (hW.trans hi)).injective
  apply Subtype.ext
  funext j
  change rawCoordinate φ i W _ j (lift φ i W _ _) = rawCoordinate φ i W _ j (moduleRes _ hW _)
  rw [lift_coordinate, rawCoordinate_restrict, lift_coordinate]
  change sectionD (toBase φ) _ _ = _
  rw [← normalized_restrict φ i (coord φ j) (coord_mem_grade φ j) hi hW]
  exact sectionD_restrict (toBase φ) hW s _

theorem toQuotient_restrict {W : (threefold φ).Opens} (hW : W ≤ V) (s : Γ(tangent (toBase φ),V)) :
    toQuotient φ i W (hW.trans hi) (moduleRes _ hW s) = moduleRes _ hW (toQuotient φ i V hi s) := by
  change (cokernel.π (radialTangent φ)).app W _ = moduleRes _ hW ((cokernel.π (radialTangent φ)).app V _)
  rw [moduleRes_app, lift_restrict]

end CycleQ2HodgeEulerTangentToQuotient
end
#print axioms CycleQ2HodgeEulerTangentToQuotient.frame_toQuotient
#print axioms CycleQ2HodgeEulerTangentToQuotient.toQuotient_restrict
