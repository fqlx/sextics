import Proposal.GeometricHodgeEulerSheaf
import Proposal.GeometricHodgeEulerTangentCoordinates
import Proposal.GeometricHodgeFermatYukawaDeterminant
import Proposal.GeometricAffineChartSections

/-!
# Four explicit projective normal lifts on the Fermat fiber

Over the i-th weight-one open, the i-th homogeneous partial normalizes to
six. Every degree-six numerator has a one-component lift through the actual
normal morphism. On the common chart the same lift has coefficient
p/(6xᵢ⁵) in its unique homogeneous slot.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeFermatNormalLifts

open AlgebraicGeometry CategoryTheory Limits Opposite MvPolynomial
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2HodgeEulerSheaf
open CycleQ2HodgeEulerTangentCoordinates (chartSection_normalized)
open CycleQ2HodgeEulerChartBinding (affineChart)
open CycleQ2HodgeAtlasLine (coordinate_restrict restrictRing)
open CycleQ2SeedSectionSheafLocal (moduleRes moduleRes_app)
open CycleQ2GenericSexticGradient (seedEvaluation universalF_seed)
open CycleQ2SeedSectionSheafLimits (sectionProductEquiv sectionProductEquiv_apply sectionProductEquiv_symm_apply)
open CycleQ2GeometricDifferentialSheaf (coefficientOn)
open CycleQ2GeometricAffineChartSections (schemeCoefficient chartSection)

abbrev ψ := seedEvaluation
def coefficient (V : (threefold ψ).Opens) : ℂ →+* Γ(threefold ψ,V) :=
  coefficientOn (threefold ψ).sheaf (schemeCoefficient (toBase ψ)) V

def invSix (V : (threefold ψ).Opens) : Γ(threefold ψ,V) := coefficient V ((6 : ℂ)⁻¹)

theorem six_invSix (V : (threefold ψ).Opens) : (6 : Γ(threefold ψ,V)) * invSix V = 1 := by
  simpa only [map_mul, map_ofNat, map_one, invSix] using
    congrArg (coefficient V) (mul_inv_cancel₀ (by norm_num : (6 : ℂ) ≠ 0))

theorem self_partial_polynomial (i : Fin 4) :
    pderiv i.castSucc (equation ψ) = C (6 : ℂ) * X i.castSucc ^ 5 := by
  change pderiv i.castSucc (MvPolynomial.map seedEvaluation _) = _
  rw [universalF_seed, CycleQ2FermatJacobian.derivative_eq]
  have h₁ : CycleQ2FermatJacobian.derivativeScalar i.castSucc = 6 := by fin_cases i <;> rfl
  have h₂ : CycleQ2FermatJacobian.cutoff i.castSucc = 5 := by fin_cases i <;> rfl
  rw [h₁, CycleQ2FermatJacobian.generator, h₂]

theorem self_partial (i : Fin 4) (V : (threefold ψ).Opens) (hi : V ≤ U ψ i) :
    normalized ψ i (partialValue ψ i.castSucc) (partial_mem ψ i.castSucc) V hi = 6 := by
  let E : MvPolynomial (Fin 5) ℂ →+* Γ(threefold ψ,V) :=
    (chartSection (affineChart ψ i) (Over.mk (homOfLE hi))).comp
      ((CycleQ2HodgeEuler.chartMap ψ i).toRingHom.comp (CycleQ2HodgeEuler.dehom i).toRingHom)
  have hX : E (X i.castSucc) = 1 := by
    change chartSection _ _ (CycleQ2HodgeEuler.chartMap ψ i (CycleQ2HodgeEuler.dehom i (X i.castSucc))) = 1
    rw [CycleQ2HodgeEuler.dehom_X_self, map_one, map_one]
  have hp := (equation_homogeneous ψ).pderiv (i := i.castSucc)
    (Nat.sub_add_cancel (show geometricWeight i.castSucc ≤ 6 by fin_cases i <;> decide))
  have he : normalized ψ i (partialValue ψ i.castSucc) (partial_mem ψ i.castSucc) V hi =
      E (pderiv i.castSucc (equation ψ)) :=
    (chartSection_normalized ψ i V hi _ hp).symm
  rw [he, self_partial_polynomial, map_mul, map_pow, hX, one_pow, mul_one]
  rw [show C (6 : ℂ) = (6 : MvPolynomial (Fin 5) ℂ) from map_ofNat _ _, map_ofNat]

variable (i : Fin 4) (V : (threefold ψ).Opens) (hi : V ≤ U ψ i) (p : cone ψ) (hp : p ∈ grade ψ 6)

def lift : Γ(raw ψ,V) :=
  (sectionProductEquiv (pieces ψ) V).symm fun a =>
    (chartFrame ψ (geometricWeight a) i V hi).symm
      (if a = i.castSucc then invSix V * normalized ψ i p hp V hi else 0)

theorem lift_frame (a : Fin 5) :
    chartFrame ψ (geometricWeight a) i V hi ((Pi.π (pieces ψ) a).app V (lift i V hi p hp)) =
      if a = i.castSucc then invSix V * normalized ψ i p hp V hi else 0 := by
  simp only [lift, sectionProductEquiv_symm_apply, LinearEquiv.apply_symm_apply]

theorem lift_normal : (normalMap ψ).app V (lift i V hi p hp) = homogeneousSection ψ p hp V := by
  apply (chartFrame ψ 6 i V hi).injective
  rw [normal_frame, homogeneousSection_coordinate]
  simp_rw [lift_frame]
  rw [Finset.sum_eq_single i.castSucc]
  · rw [if_pos rfl, self_partial, ← mul_assoc, six_invSix, one_mul]
  · intro a _ ha
    rw [if_neg ha, mul_zero]
  · simp

theorem lift_restrict {W : (threefold ψ).Opens} (h : W ≤ V) :
    moduleRes (raw ψ) h (lift i V hi p hp) = lift i W (h.trans hi) p hp := by
  apply (sectionProductEquiv (pieces ψ) W).injective
  funext a
  rw [sectionProductEquiv_apply, sectionProductEquiv_apply, ← moduleRes_app]
  apply (chartFrame ψ (geometricWeight a) i W (h.trans hi)).injective
  have hr := coordinate_restrict (cocycle ψ (geometricWeight a)) i hi h
    ((Pi.π (pieces ψ) a).app V (lift i V hi p hp))
  refine hr.trans ?_
  change restrictRing (X := threefold ψ) h
    (chartFrame ψ (geometricWeight a) i V hi ((Pi.π (pieces ψ) a).app V (lift i V hi p hp))) = _
  rw [lift_frame, lift_frame]
  by_cases ha : a = i.castSucc
  · simp only [if_pos ha, map_mul]
    have hc : restrictRing (X := threefold ψ) h (invSix V) = invSix W :=
      (ConcreteCategory.congr_hom ((CycleQ2GeometricDifferentialSheaf.coefficientMap (threefold ψ).sheaf
        (schemeCoefficient (toBase ψ))).naturality (homOfLE h).op) ((6 : ℂ)⁻¹)).symm
    exact congrArg₂ (·*·) hc (normalized_restrict ψ i p hp hi h)
  · simp only [if_neg ha, map_zero]

/-- In the pivot-zero frame these are the inverse homogeneous partials. -/
def inversePartial (h₀ : V ≤ U ψ 0) : Γ(threefold ψ,V) :=
  invSix V * ((transition ψ 0 i V h₀ hi) ^ (-5 : ℤ)).val

private theorem unit_powers (u : Γ(threefold ψ,V)ˣ) :
    u.val ^ 6 * (u ^ (-5 : ℤ)).val = u.val := by
  have h : u ^ (6 : ℤ) * u ^ (-5 : ℤ) = u := by rw [← zpow_add]; norm_num
  exact congrArg Units.val h

theorem read_lift (h : ∀ j : Fin 4, V ≤ U ψ j) (a : Fin 5) :
    chartFrame ψ (geometricWeight a) 0 V (h 0) ((Pi.π (pieces ψ) a).app V (lift i V hi p hp)) =
      CycleQ2HodgeFermatYukawaDeterminant.lift
        (fun j => inversePartial j V (h j) (h 0)) i (normalized ψ 0 p hp V (h 0)) a := by
  classical
  rw [chartFrame_transition ψ (geometricWeight a) 0 i V (h 0) hi, lift_frame]
  by_cases ha : a = i.castSucc
  · subst a
    simp only [CycleQ2HodgeFermatYukawaDeterminant.lift, if_pos rfl,
      CycleQ2SeedFermatProj.geometricWeight_castSucc, Nat.cast_one, zpow_one]
    let u := transition ψ 0 i V (h 0) hi
    have hc : normalized ψ 0 p hp V (h 0) = u.val ^ 6 * normalized ψ i p hp V hi :=
      normalized_change ψ 0 i p hp V (h 0) hi
    rw [hc]
    change u.val * (invSix V * _) = (u.val ^ 6 * _) * (invSix V * (u ^ (-5 : ℤ)).val)
    calc
      u.val * (invSix V * normalized ψ i p hp V hi) =
          (u.val ^ 6 * (u ^ (-5 : ℤ)).val) * (invSix V * normalized ψ i p hp V hi) :=
        congrArg (fun z => z * (invSix V * normalized ψ i p hp V hi)) (unit_powers V u).symm
      _ = _ := by ring
  · simp only [if_neg ha, mul_zero, CycleQ2HodgeFermatYukawaDeterminant.lift]

end CycleQ2HodgeFermatNormalLifts
end

#print axioms CycleQ2HodgeFermatNormalLifts.lift_normal
#print axioms CycleQ2HodgeFermatNormalLifts.read_lift
