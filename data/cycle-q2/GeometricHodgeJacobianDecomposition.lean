import Proposal.GeometricHodgeJacobianInjective

/-!
# The full degree-six Jacobian decomposition of the normal deformation group

All global coordinate velocities and all normal sections are accounted for by
their graded cone numerators. Projection to the three original characters
gives the direct decomposition of the derived deformation group, by a map
whose value on each polynomial is its normal connecting class.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeJacobianDecomposition

open AlgebraicGeometry CategoryTheory Limits TopologicalSpace MvPolynomial
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEulerSheaf CycleQ2HodgeThreefoldTwist
open CycleQ2HodgeNormalDeformations CycleQ2HodgeNormalCohomology CycleQ2HodgeInfinitesimalQuotient
open CycleQ2IncidenceNormalForm (fullGrading fullGrading_weight)
open CycleQ2GeometricIncidenceProj (geometricWeight geometricWeight_weight homogeneous_of_character)
open CycleQ2HodgeJacobianConnecting (jacobianClass jacobianClass_direction)
open CycleQ2HodgeJacobianInjective (jacobian_zero_of_connecting)
open CycleQ2HiggsJacobianFrames (gradedPiece quotientMap jacobian)
open CycleQ2HodgeTwistConeSections (gradedConeEquiv)
open CycleQ2GenericSexticGradient (CoeffRing)

variable (φ : CoeffRing →+* ℂ) (hg : IsUnit (φ goodParameter))
local instance : Module ℂ (H φ (rawTangent φ) 1) :=
  CycleQ2GeometricSheafCohomologyScalar.cohomologyModule (threefold φ).sheaf
    (CycleQ2GeometricAffineChartSections.schemeCoefficient (toBase φ)) (rawTangent φ) 1 ⊤

private abbrev Family := (χ : ZMod 3) → Directions ℂ χ
private abbrev combined (p : Family) := ∑ χ, (p χ).val

private theorem combined_weight (p : Family) : (combined p).IsWeightedHomogeneous geometricWeight 6 :=
  (weightedHomogeneousSubmodule ℂ geometricWeight 6).sum_mem fun χ _ =>
    homogeneous_of_character (p χ).property

private theorem character_combined (p : Family) (χ : ZMod 3) :
    weightedHomogeneousComponent fullGrading (6,χ) (combined p) = (p χ).val := by
  rw [combined, map_sum, Finset.sum_eq_single χ]
  · exact (p χ).property.weightedHomogeneousComponent_same
  · intro ξ _ hξ
    exact (p ξ).property.weightedHomogeneousComponent_ne _ (fun e => hξ (congrArg Prod.snd e).symm)
  · simp

private def split (p : MvPolynomial (Fin 5) ℂ) : Family := fun χ =>
  ⟨_, weightedHomogeneousComponent_mem fullGrading p (6,χ)⟩

private theorem combined_split (p : MvPolynomial (Fin 5) ℂ) (hp : p.IsWeightedHomogeneous geometricWeight 6) :
    combined (split p) = p := by
  classical
  ext d
  simp only [combined, split, coeff_sum, coeff_weightedHomogeneousComponent]
  by_cases hd : coeff d p = 0
  · simp [hd]
  · have hw := hp hd
    rw [geometricWeight_weight] at hw
    simp [fullGrading_weight, hw]

private theorem combined_section (h : IsUnit (φ vertexCoefficient)) (p : Family) :
    (∑ χ, directionSection φ (p χ) ⊤) =
      homogeneousSection φ (quotient φ (combined p)) (quotient_mem_grade φ _ (combined_weight p)) ⊤ := by
  let a (χ : ZMod 3) : grade φ 6 :=
    ⟨quotient φ (p χ).val, quotient_mem_grade φ _ (homogeneous_of_character (p χ).property)⟩
  change ∑ χ, (gradedConeEquiv φ h 6) (a χ) = (gradedConeEquiv φ h 6) _
  rw [← map_sum]
  apply congrArg (gradedConeEquiv φ h 6)
  apply Subtype.ext
  change (∑ χ, a χ : grade φ 6).val = quotient φ (combined p)
  rw [Submodule.coe_sum, combined, map_sum]
  rfl

def total : ((χ : ZMod 3) → gradedPiece φ 6 χ) →ₗ[ℂ] H φ (rawTangent φ) 1 :=
  ∑ χ, (jacobianClass φ χ hg).comp (LinearMap.proj χ)

private theorem total_directions (p : Family) :
    total φ hg (fun χ => directionClass φ χ (p χ)) =
      connecting φ hg (homogeneousSection φ (quotient φ (combined p))
        (quotient_mem_grade φ _ (combined_weight p)) ⊤) := by
  have h := hg
  rw [goodParameter, map_mul, IsUnit.mul_iff] at h
  simp only [total, LinearMap.sum_apply, LinearMap.coe_comp, Function.comp_apply, LinearMap.proj_apply,
    jacobianClass_direction]
  rw [← map_sum, combined_section φ h.2]

theorem total_injective : Function.Injective (total φ hg) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a
  choose p hp using fun χ => directionClass_surjective φ χ (a χ)
  rw [show a = fun χ => directionClass φ χ (p χ) from (funext hp).symm, total_directions]
  intro h
  have hz := jacobian_zero_of_connecting φ hg _ (combined_weight p) h
  have hm : combined p ∈ jacobian φ := Ideal.Quotient.eq_zero_iff_mem.mp hz
  funext χ
  apply Subtype.ext
  change quotientMap φ (p χ).val = 0
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  rw [← character_combined p χ]
  exact CycleQ2HiggsJacobianMembership.component_mem φ 6 χ hm

theorem total_surjective : Function.Surjective (total φ hg) := by
  have h := hg
  rw [goodParameter, map_mul, IsUnit.mul_iff] at h
  have hv (j : Fin 5) : Subsingleton (H φ (pieces φ j) 1) := by
    haveI := (CycleQ2HodgeTwistTorusChart.ordinary_vanishing φ h.2 (geometricWeight j)).1
    exact (CycleQ2GeometricSheafCohomologyRestriction.terminalCohomologyEquiv
      (Opens.grothendieckTopology (threefold φ)) (Add φ (pieces φ j)) ⊤ isTerminalTop 1).injective.subsingleton
  intro x
  obtain ⟨s,hs⟩ := connecting_surjective φ hg hv x
  obtain ⟨a,ha⟩ := (gradedConeEquiv φ h.2 6).surjective s
  obtain ⟨p,hp,he⟩ := a.property
  let q := split p
  have hn : (⟨quotient φ (combined q), quotient_mem_grade φ _ (combined_weight q)⟩ : grade φ 6) = a := by
    apply Subtype.ext
    exact (congrArg (quotient φ) (combined_split p hp)).trans he
  refine ⟨fun χ => directionClass φ χ (q χ), ?_⟩
  rw [total_directions]
  exact (congrArg (connecting φ hg) ((congrArg (gradedConeEquiv φ h.2 6) hn).trans ha)).trans hs

def normalDeformationEquiv : ((χ : ZMod 3) → gradedPiece φ 6 χ) ≃ₗ[ℂ] H φ (rawTangent φ) 1 :=
  LinearEquiv.ofBijective (total φ hg) ⟨total_injective φ hg, total_surjective φ hg⟩

end CycleQ2HodgeJacobianDecomposition
end

#print axioms CycleQ2HodgeJacobianDecomposition.normalDeformationEquiv
