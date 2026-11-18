import Proposal.GeometricHodgeJacobianConnecting
import Proposal.GeometricHodgeTwistConeSections
import Proposal.GeometricHodgeConeDirections

/-!
# Injectivity of the Jacobian classes on the moving smooth threefold

A vanishing normal connecting class has a global lift to the five weighted
coordinate twists. Their actual global-section calculation supplies polynomial
numerators for the five velocities. Injectivity of the homogeneous section
map then identifies the original numerator with their gradient contraction
in the cone. Passing to the Jacobian ring kills that contraction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeJacobianInjective

open AlgebraicGeometry CategoryTheory Limits MvPolynomial
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEulerSheaf CycleQ2HodgeThreefoldTwist
open CycleQ2HodgeTwistRatios CycleQ2HodgeAtlasLine CycleQ2HodgeNormalDeformations
open CycleQ2HodgeInfinitesimalQuotient CycleQ2HodgeNormalCohomology
open CycleQ2GeometricIncidenceProj (geometricWeight homogeneous_of_character)
open CycleQ2HodgeJacobianConnecting (jacobianClass jacobianClass_direction)
open CycleQ2HiggsJacobianFrames (gradedPiece quotientMap)
open CycleQ2HodgeTwistConeSections (gradedConeEquiv)
open CycleQ2GenericSexticGradient (CoeffRing)

variable (φ : CoeffRing →+* ℂ) (χ : ZMod 3)

private abbrev Polys := Fin 5 → MvPolynomial (Fin 5) ℂ
private abbrev normalPoly (v : Polys) := ∑ j, v j * pderiv j (equation φ)

private theorem normalPoly_weight (v : Polys)
    (hv : ∀ j, (v j).IsWeightedHomogeneous geometricWeight (geometricWeight j)) :
    (normalPoly φ v).IsWeightedHomogeneous geometricWeight 6 := by
  apply (weightedHomogeneousSubmodule ℂ geometricWeight 6).sum_mem
  intro j _
  have h : geometricWeight j ≤ 6 := by fin_cases j <;> decide
  simpa only [Nat.add_sub_of_le h] using
    (hv j).mul ((equation_homogeneous φ).pderiv (Nat.sub_add_cancel h))

private theorem lift_has_numerators (h : IsUnit (φ vertexCoefficient)) (v : Γ(raw φ,⊤)) :
    ∃ p : Polys, ∃ hp : ∀ j, (p j).IsWeightedHomogeneous geometricWeight (geometricWeight j),
      ∀ j, (Pi.π (pieces φ) j).app ⊤ v =
        homogeneousSection φ (quotient φ (p j)) (quotient_mem_grade φ _ (hp j)) ⊤ := by
  have hl (j : Fin 5) : ∃ p : MvPolynomial (Fin 5) ℂ,
      ∃ hp : p.IsWeightedHomogeneous geometricWeight (geometricWeight j),
        (Pi.π (pieces φ) j).app ⊤ v = homogeneousSection φ (quotient φ p) (quotient_mem_grade φ p hp) ⊤ := by
    obtain ⟨a,ha⟩ := (gradedConeEquiv φ h (geometricWeight j)).surjective ((Pi.π (pieces φ) j).app ⊤ v)
    obtain ⟨p,hp,he⟩ := a.property
    have he' : a = (⟨quotient φ p, quotient_mem_grade φ p hp⟩ : grade φ (geometricWeight j)) :=
      Subtype.ext he.symm
    subst a
    exact ⟨p,hp,ha.symm⟩
  choose p hp he using hl
  exact ⟨p,hp,he⟩

private theorem normal_of_numerators (b : Γ(raw φ,⊤)) (v : Polys)
    (hv : ∀ j, (v j).IsWeightedHomogeneous geometricWeight (geometricWeight j))
    (he : ∀ j, (Pi.π (pieces φ) j).app ⊤ b =
      homogeneousSection φ (quotient φ (v j)) (quotient_mem_grade φ _ (hv j)) ⊤) :
    (normalMap φ).app ⊤ b = homogeneousSection φ (quotient φ (normalPoly φ v))
       (quotient_mem_grade φ _ (normalPoly_weight φ v hv)) ⊤ := by
  apply component_injective (cocycle φ 6) ⊤
  intro i
  rw [normal_component]
  simp only [he, homogeneousSection, component_pack]
  change ∑ j, normalized φ i (quotient φ (pderiv j (equation φ))) _ _ _ *
    normalized φ i (quotient φ (v j)) _ _ _ = normalized φ i (quotient φ (normalPoly φ v)) _ _ _
  simp_rw [← evaluate_homogeneous, normalPoly, map_sum, map_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem jacobian_zero_of_connecting (hg : IsUnit (φ goodParameter))
    (p : MvPolynomial (Fin 5) ℂ) (hp : p.IsWeightedHomogeneous geometricWeight 6)
    (hδ : connecting φ hg (homogeneousSection φ (quotient φ p) (quotient_mem_grade φ p hp) ⊤) = 0) :
    quotientMap φ p = 0 := by
  have h := hg
  rw [goodParameter, map_mul, IsUnit.mul_iff] at h
  obtain ⟨b,hb⟩ := (connecting_zero_iff φ hg _).mp hδ
  obtain ⟨v,hv,he⟩ := lift_has_numerators φ h.2 b
  let P : grade φ 6 := ⟨quotient φ p, quotient_mem_grade φ _ hp⟩
  let Q : grade φ 6 := ⟨quotient φ (normalPoly φ v), quotient_mem_grade φ _ (normalPoly_weight φ v hv)⟩
  have heq : (gradedConeEquiv φ h.2 6) P = (gradedConeEquiv φ h.2 6) Q :=
    hb.symm.trans (normal_of_numerators φ b v hv he)
  have hh := congrArg (fun s : grade φ 6 => CycleQ2HodgeConeDirections.coneToJacobian φ s.val)
    ((gradedConeEquiv φ h.2 6).injective heq)
  change quotientMap φ p = quotientMap φ (normalPoly φ v) at hh
  have hj (j : Fin 5) : quotientMap φ (pderiv j (equation φ)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨j,rfl⟩)
  simpa only [normalPoly, map_sum, map_mul, hj, mul_zero, Finset.sum_const_zero] using hh

theorem jacobianClass_injective (hg : IsUnit (φ goodParameter)) :
    Function.Injective (jacobianClass φ χ hg) := by
  apply (injective_iff_map_eq_zero _).mpr
  intro a
  obtain ⟨p,rfl⟩ := directionClass_surjective φ χ a
  rw [jacobianClass_direction]
  intro hδ
  exact Subtype.ext (jacobian_zero_of_connecting φ hg p.val (homogeneous_of_character p.property) hδ)

end CycleQ2HodgeJacobianInjective
end

#print axioms CycleQ2HodgeJacobianInjective.jacobianClass_injective
