import Proposal.GeometricHodgeEulerSheaf
import Proposal.GeometricHodgeInfinitesimalQuotient

/-!
# Actual polynomial directions and the projective normal map

The homogeneous coordinate velocities on the affine cone give sections
of the five Euler twists. The genuine normal sheaf morphism sends them
to the global section of their derivative of the full sextic. This binds
the polynomial deformation quotient to the same morphism whose connecting
map gives the hypersurface deformation class.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeNormalDeformations

open AlgebraicGeometry CategoryTheory Limits MvPolynomial Opposite
open CycleQ2GeometricIncidenceProj CycleQ2GeometricHodgeThreefold
open CycleQ2HodgeEulerSheaf CycleQ2HodgeThreefoldTwist CycleQ2HodgeAtlasLine
open CycleQ2HodgeInfinitesimalQuotient CycleQ2HodgeTwistRatios
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2SeedSectionSheafLimits (sectionProductEquiv sectionProductEquiv_symm_apply)
open CycleQ2SeedSectionSheafLocal (moduleRes)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) {χ : ZMod 3}

def evaluate (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) :
    MvPolynomial (Fin 5) R →+* Γ(threefold φ,V) :=
  (sectionMap φ i V hi).comp ((CycleQ2HodgeEulerChartBinding.chartEquiv φ i).symm.toRingHom.comp
    ((CycleQ2HodgeEuler.chartMap φ i).toRingHom.comp (CycleQ2HodgeEuler.dehom i).toRingHom))

theorem evaluate_homogeneous (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    {n : ℕ} (p : MvPolynomial (Fin 5) R) (hp : p.IsWeightedHomogeneous geometricWeight n) :
    evaluate φ i V hi p = normalized φ i (quotient φ p) (quotient_mem_grade φ p hp) V hi := by
  change sectionMap φ i V hi ((CycleQ2HodgeEulerChartBinding.chartEquiv φ i).symm
      (CycleQ2HodgeEuler.chartMap φ i (CycleQ2HodgeEuler.dehom i p))) =
    sectionMap φ i V hi (CycleQ2HodgeEulerChartBinding.fraction φ i n p hp)
  exact congrArg (sectionMap φ i V hi) ((CycleQ2HodgeEulerChartBinding.chartEquiv φ i).symm_apply_eq.mpr
    (CycleQ2HodgeEulerChartBinding.chartEquiv_fraction φ i n p hp).symm)

theorem velocity_weight (v : Velocities R χ) (j : Fin 5) :
    (v j : MvPolynomial (Fin 5) R).IsWeightedHomogeneous geometricWeight (geometricWeight j) := by
  have hw : (CycleQ2IncidenceNormalForm.fullGrading j).1 = geometricWeight j := by fin_cases j <;> rfl
  rw [← hw]
  exact homogeneous_of_character (v j).property

def velocitySection (v : Velocities R χ) (V : (threefold φ).Opens) : Γ(raw φ,V) :=
  (sectionProductEquiv (pieces φ) V).symm fun j =>
    homogeneousSection φ (quotient φ (v j)) (quotient_mem_grade φ _ (velocity_weight v j)) V

def directionSection (a : Directions R χ) (V : (threefold φ).Opens) : Γ(twist φ 6,V) :=
  homogeneousSection φ (quotient φ a.val) (quotient_mem_grade φ _ (homogeneous_of_character a.property)) V

theorem derivative_frame (v : Velocities R χ) (i : Fin 4) (V : (threefold φ).Opens)
    (hi : V ≤ U φ i) :
    chartFrame φ 6 i V hi ((normalMap φ).app V (velocitySection φ v V)) =
      chartFrame φ 6 i V hi (directionSection φ (derivative φ χ v) V) := by
  rw [normal_frame]
  simp only [velocitySection, sectionProductEquiv_symm_apply, homogeneousSection_coordinate,
    directionSection]
  change ∑ j, normalized φ i (quotient φ (pderiv j (equation φ))) _ V hi *
      normalized φ i (quotient φ (v j)) _ V hi =
    normalized φ i (quotient φ (velocityDerivation v (FiberPolynomial φ))) _ V hi
  simp_rw [← evaluate_homogeneous, velocityDerivation_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

theorem normal_velocity (v : Velocities R χ) (V : (threefold φ).Opens) :
    (normalMap φ).app V (velocitySection φ v V) = directionSection φ (derivative φ χ v) V := by
  apply component_injective (cocycle φ 6) V
  intro i
  rw [normal_component]
  simp only [velocitySection, sectionProductEquiv_symm_apply, directionSection, homogeneousSection,
    component_pack]
  change ∑ j, normalized φ i (quotient φ (pderiv j (equation φ))) _ _ _ *
      normalized φ i (quotient φ (v j)) _ _ _ =
    normalized φ i (quotient φ (velocityDerivation v (FiberPolynomial φ))) _ _ _
  simp_rw [← evaluate_homogeneous, velocityDerivation_apply, map_sum, map_mul]
  exact Finset.sum_congr rfl fun _ _ => mul_comm _ _

end CycleQ2HodgeNormalDeformations
end

#print axioms CycleQ2HodgeNormalDeformations.normal_velocity
