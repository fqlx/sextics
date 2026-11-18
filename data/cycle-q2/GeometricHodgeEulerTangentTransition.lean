import Proposal.GeometricHodgeEulerTangentRestriction
import Proposal.GeometricHodgeEulerOverlapBinding

/-! Intrinsic restriction on the native double intersection computes the
weighted quotient rule on the original raw ambient vector. Both coordinate
charts use their actual inclusions into the moving complex threefold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerTangentSheaf

open AlgebraicGeometry CategoryTheory Opposite
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold coordinateOpen toBase)
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding CycleQ2HodgeEulerOverlapBinding

variable (φ : CoeffRing →+* ℂ) (i k : Fin 4)

/-- Restricting native tangent sections from the first projective chart
is ordinary localization of their coordinate derivation. -/
theorem recover_overlap (s : Γ(tangent (toBase φ),coordinateOpen φ i)) :
    recover (overlapChart φ i k) (toBase φ) (overlapChart_overBase φ i k)
        ((tangent (toBase φ)).val.map (homOfLE (show intersection φ i k ≤ coordinateOpen φ i
          from inf_le_left)).op s) =
      CycleQ2LocalizationDerivation.extend (S := overlap φ i k)
        (Submonoid.powers (coordinate φ i k.castSucc))
        (recover (affineChart φ i) (toBase φ) (affineChart_overBase φ i) s) := by
  apply CycleQ2LocalizationDerivation.extend_unique
  intro a
  exact recover_restriction (affineChart φ i) (overlapChart φ i k) (toBase φ)
    (affineChart_overBase φ i) (overlapChart_overBase φ i k) inf_le_left _
    (overlapChart_to_first φ i k) s a

/-- The other inclusion differentiates the actual transition homomorphism. -/
theorem recover_overlap_second (s : Γ(tangent (toBase φ),coordinateOpen φ k)) (a : chart φ k) :
    recover (overlapChart φ i k) (toBase φ) (overlapChart_overBase φ i k)
        ((tangent (toBase φ)).val.map (homOfLE (show intersection φ i k ≤ coordinateOpen φ k
          from inf_le_right)).op s) (overlapMap φ i k a) =
      overlapMap φ i k (recover (affineChart φ k) (toBase φ) (affineChart_overBase φ k) s a) :=
  recover_restriction (affineChart φ k) (overlapChart φ i k) (toBase φ)
    (affineChart_overBase φ k) (overlapChart_overBase φ i k) inf_le_right _
    (overlapChart_to_second φ i k) s a

/-- Evaluate the restriction of a native tangent section represented on
chart i by v on each of the original chart k functions. -/
theorem quotientTangentSections_overlap (v : RawTangent φ i) (j : Fin 5) :
    let W := intersection φ i k
    let D := (tangent (toBase φ)).val.map (homOfLE (show W ≤ coordinateOpen φ i from inf_le_left)).op
      (quotientTangentSections φ i (Submodule.Quotient.mk v))
    evaluate (toBase φ) D (differential (overlapChart φ i k) (toBase φ)
        (overlapMap φ i k (coordinate φ k j))) =
      functions (overlapChart φ i k) (invPivot φ i k ^ geometricWeight j *
        (algebraMap (chart φ i) (overlap φ i k) (v.val j) -
          (geometricWeight j : overlap φ i k) * invPivot φ i k * localCoordinate φ i k j *
            algebraMap (chart φ i) (overlap φ i k) (v.val k.castSucc))) := by
  dsimp only
  rw [← recover_apply _ _ (overlapChart_overBase φ i k), recover_overlap]
  change functions _ (CycleQ2LocalizationDerivation.extend _
      ((affineTangentEquiv (affineChart φ i) (toBase φ) (affineChart_overBase φ i)).symm
        ((affineTangentEquiv (affineChart φ i) (toBase φ) (affineChart_overBase φ i))
          (tangentQuotientEquiv φ i (Submodule.Quotient.mk v)))) _) = _
  rw [Equiv.symm_apply_apply, rawTangent_overlap]

end CycleQ2HodgeEulerTangentSheaf
end

#print axioms CycleQ2HodgeEulerTangentSheaf.recover_overlap_second
#print axioms CycleQ2HodgeEulerTangentSheaf.quotientTangentSections_overlap
