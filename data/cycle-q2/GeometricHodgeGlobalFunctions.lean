import Proposal.GeometricHodgeTwistConeSections
import Proposal.GeometricHodgeEulerTangentCoordinates
import Proposal.GeometricIncidenceFamilyContainment

/-! # The original moving projective threefold has only constant global functions

Multiplication by the degree-zero homogeneous section one sends a regular
function to a global section of O(0). The actual cone-section comparison
expresses that section by a degree-zero numerator. Positivity of every
coordinate weight makes its polynomial constant, and the affine chart
frames identify that constant with the original regular function.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeGlobalFunctions

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial TopologicalSpace
  CycleQ2GeometricHodgeThreefold CycleQ2GeometricIncidenceProj CycleQ2HodgeTwistConeSections
  CycleQ2HodgeEulerTangentCoordinates CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding
  CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios CycleQ2GeometricAffineChartSections
  CycleQ2GeometricDifferentialSheaf CycleQ2GeometricTwistedDifferential
open CycleQ2SeedSectionSheafLocal (moduleRes)
open CycleQ2GenericSexticGradient (CoeffRing)

private theorem degree_zero (p : MvPolynomial (Fin 5) ℂ) (hp : p.IsWeightedHomogeneous geometricWeight 0) :
    p = C (coeff 0 p) := by
  classical
  ext d
  by_cases hd : d = 0
  · subst d; simp
  · have h0 : coeff d p = 0 := by
      by_contra h
      have he := hp h
      apply hd
      ext j
      have hj := Finsupp.le_weight geometricWeight
        (Nat.ne_of_gt (CycleQ2IncidenceFamilyContainment.geometricWeight_pos j)) d
      rw [he] at hj
      exact Nat.eq_zero_of_le_zero hj
    simp [h0,hd,Ne.symm hd]

variable (φ : CoeffRing →+* ℂ)
private abbrev c := schemeCoefficient (toBase φ)

private theorem constant_frame (b : ℂ) (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) :
    chartFrame φ 0 i V hi (homogeneousSection φ (quotient φ (C b))
      (quotient_mem_grade φ _ (isWeightedHomogeneous_C geometricWeight b)) V) =
      coefficientOn (threefold φ).sheaf (c φ) V b := by
  rw [homogeneousSection_coordinate, ← chartSection_normalized]
  rw [show dehom i (C b) = C b from aeval_C _ _]
  exact chartSection_complex (affineChart φ i) (toBase φ) (affineChart_overBase φ i) (Over.mk (homOfLE hi)) b

private abbrev baseSection (b : ℂ) (V : (threefold φ).Opens) :=
  homogeneousSection φ (quotient φ (C b)) (quotient_mem_grade φ _ (isWeightedHomogeneous_C geometricWeight b)) V

theorem globalFunction (hv : IsUnit (φ vertexCoefficient)) (s : Γ(threefold φ,⊤)) :
    ∃ b : ℂ, s = coefficientOn (threefold φ).sheaf (c φ) ⊤ b := by
  let A := baseSection φ 1 ⊤
  obtain ⟨a,ha⟩ := (gradedConeEquiv φ hv 0).surjective (s • A)
  obtain ⟨p,hp,he⟩ := a.property
  let b := coeff 0 p
  have he' : a.val = quotient φ (C b) := he.symm.trans (congrArg (quotient φ) (degree_zero p hp))
  have he'' : a = ⟨quotient φ (C b),quotient_mem_grade φ _ (isWeightedHomogeneous_C geometricWeight b)⟩ :=
    Subtype.ext he'
  rw [he''] at ha
  refine ⟨b,?_⟩
  apply (threefold φ).sheaf.eq_of_locally_eq' (U φ) ⊤ (fun _ => homOfLE le_top)
    (coordinateOpens_cover φ hv).ge
  intro i
  let V := U φ i
  let h : V ≤ (⊤ : (threefold φ).Opens) := le_top
  have hV := congrArg ((chartFrame φ 0 i V le_rfl) ∘ moduleRes (twist φ 0) h) ha
  change (chartFrame φ 0 i V _) (moduleRes _ h (baseSection φ b ⊤)) =
    (chartFrame φ 0 i V _) ((twist φ 0).val.map (homOfLE h).op (s • A)) at hV
  rw [(twist φ 0).val.map_smul, map_smul] at hV
  change (chartFrame φ 0 i V _) (moduleRes _ h (baseSection φ b ⊤)) =
    (threefold φ).presheaf.map (homOfLE h).op s * (chartFrame φ 0 i V _) (moduleRes _ h (baseSection φ 1 ⊤)) at hV
  simp only [baseSection, homogeneousSection_restrict, constant_frame, map_one, mul_one] at hV
  exact hV.symm.trans (coefficientOn_restrict (threefold φ).sheaf (c φ) h b).symm

end CycleQ2HodgeGlobalFunctions
end
#print axioms CycleQ2HodgeGlobalFunctions.globalFunction
