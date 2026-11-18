import Proposal.GeometricHodgeEquationShear
import Proposal.GeometricHodgeThreefoldGradient

/-!
# First-order points of the original moving chart

Moving the four affine coordinate functions by epsilon times a tuple gives
a homomorphism on the actual dual polynomial ring. It factors through the
hypersurface F − epsilon p precisely when the normal derivative of the
coordinate tuple equals the normalized direction p. The epsilon coefficient
on every function is the original Jacobian derivative, including after
any further map out of the chart.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeKSChartPoints

open MvPolynomial CycleQ2GeometricSurfaceFirstOrder CycleQ2HodgeEuler
open CycleQ2GenericSexticGradient (CoeffRing)

variable {K S : Type} [CommRing K] [CommRing S]
private abbrev P (K : Type) [CommRing K] := MvPolynomial (Fin 4) K

def derivative (f : P K →+* S) (v : Fin 4 → S) (p : P K) : S :=
  ∑ j, v j * f (pderiv j p)

theorem derivative_mul (f : P K →+* S) (v : Fin 4 → S) (p q : P K) :
    derivative f v (p*q) = f p * derivative f v q + derivative f v p * f q := by
  rw [add_comm (f p * derivative f v q) (derivative f v p * f q)]
  simp only [derivative, pderiv_mul, map_add, map_mul, mul_add, Finset.sum_add_distrib,
    Finset.mul_sum, Finset.sum_mul]
  apply congrArg₂ (·+·)
  · exact Finset.sum_congr rfl fun _ _ => by ring
  · exact Finset.sum_congr rfl fun _ _ => by ring

def point (f : P K →+* S) (v : Fin 4 → S) : Dual (P K) →+* Dual S where
  toFun a := (f a.fst, f a.snd + derivative f v a.fst)
  map_one' := by
    apply TrivSqZeroExt.ext
    · exact map_one _
    · simp [derivative]
  map_mul' a b := by
    apply TrivSqZeroExt.ext
    · exact map_mul _ _ _
    · change f (a.fst * b.snd + a.snd * b.fst) + derivative f v (a.fst * b.fst) =
        f a.fst * (f b.snd + derivative f v b.fst) + (f a.snd + derivative f v a.fst) * f b.fst
      rw [derivative_mul, map_add, map_mul, map_mul]
      ring
  map_zero' := by
    apply TrivSqZeroExt.ext
    · exact map_zero _
    · simp [derivative]
  map_add' a b := by
    apply TrivSqZeroExt.ext
    · exact map_add _ _ _
    · change f (a.snd+b.snd) + derivative f v (a.fst+b.fst) =
        (f a.snd + derivative f v a.fst) + (f b.snd + derivative f v b.fst)
      simp only [derivative, map_add, mul_add, Finset.sum_add_distrib]
      abel

@[simp] theorem derivative_X (f : P K →+* S) (v : Fin 4 → S) (j : Fin 4) :
    derivative f v (X j) = v j := by
  classical
  rw [derivative, Finset.sum_eq_single j]
  · rw [pderiv_X_self, map_one, mul_one]
  · intro k _ hk
    rw [pderiv_X_of_ne hk.symm, map_zero, mul_zero]
  · simp

theorem factor_iff (f : P K →+* S) (v : Fin 4 → S) (F p : P K) (hF : f F = 0) :
    deformationIdeal F p ≤ RingHom.ker (point f v) ↔ derivative f v F = f p := by
  rw [deformationIdeal, Ideal.span_le, Set.singleton_subset_iff]
  change point f v (relation F p) = 0 ↔ _
  constructor
  · intro h
    have hz := congrArg TrivSqZeroExt.snd h
    change f (-p) + derivative f v F = 0 at hz
    rw [map_neg] at hz
    exact sub_eq_zero.mp (by simpa only [sub_eq_add_neg, add_comm] using hz)
  · intro h
    apply TrivSqZeroExt.ext
    · exact hF
    · change f (-p) + derivative f v F = 0
      rw [map_neg, h, neg_add_cancel]

variable (φ : CoeffRing →+* K) (i : Fin 4) (ρ : chart φ i →+* S)
abbrev chartPoint := ρ.comp (chartMap φ i).toRingHom

def deformationPoint (p : MvPolynomial (Fin 5) K) (v : Fin 4 → S)
    (hv : derivative (chartPoint φ i ρ) v (F φ i) = chartPoint φ i ρ (dehom i p)) :
    Deformation (F φ i) (dehom i p) →+* Dual S :=
  Ideal.Quotient.lift _ (point (chartPoint φ i ρ) v) ((factor_iff _ _ _ _
    (show ρ (chartMap φ i (F φ i)) = 0 by rw [chartMap_F, map_zero])).mpr hv)

/-- The actual smooth-fiber gradient makes every polynomial direction lift on each chart. -/
theorem exists_velocity (hg : IsUnit (φ CycleQ2GenericSexticGradient.gradientOpen)) (p : MvPolynomial (Fin 5) K) :
    ∃ v, derivative (chartPoint φ i ρ) v (F φ i) = chartPoint φ i ρ (dehom i p) := by
  obtain ⟨c,hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp ((Ideal.eq_top_iff_one _).mp
    (CycleQ2GeometricHodgeThreefold.chartGradient_span φ hg i))
  let t := chartPoint φ i ρ (dehom i p)
  refine ⟨fun j => t * ρ (c j), ?_⟩
  calc
    _ = t * ρ (∑ j : Fin 4, c j * chartMap φ i (pderiv j (F φ i))) := by
      rw [map_sum, Finset.mul_sum]
      exact Finset.sum_congr rfl fun _ _ => by rw [map_mul]; exact mul_assoc _ _ _
    _ = t := by rw [hc, map_one, mul_one]

theorem deformationPoint_coordinates (p : MvPolynomial (Fin 5) K) (v : Fin 4 → S) (hv)
    (j : Fin 4) : deformationPoint φ i ρ p v hv (Ideal.Quotient.mk _ (TrivSqZeroExt.inl (X j))) =
      (chartPoint φ i ρ (X j), v j) := by
  apply TrivSqZeroExt.ext
  · rfl
  · change chartPoint φ i ρ 0 + derivative (chartPoint φ i ρ) v (X j) = v j
    rw [map_zero, zero_add, derivative_X]

theorem deformationPoint_epsilon (p : MvPolynomial (Fin 5) K) (v : Fin 4 → S) (hv) :
    deformationPoint φ i ρ p v hv (Ideal.Quotient.mk _ (TrivSqZeroExt.inr 1)) = TrivSqZeroExt.inr 1 := by
  apply TrivSqZeroExt.ext
  · exact map_zero _
  · change chartPoint φ i ρ 1 + derivative (chartPoint φ i ρ) v 0 = 1
    simp [derivative]

theorem deformationPoint_dualScalars (p : MvPolynomial (Fin 5) K) (v : Fin 4 → S) (hv) (a b : K) :
    deformationPoint φ i ρ p v hv (Ideal.Quotient.mk _ ((C a, C b) : Dual (P K))) =
      (chartPoint φ i ρ (C a), chartPoint φ i ρ (C b)) := by
  apply TrivSqZeroExt.ext
  · rfl
  · change chartPoint φ i ρ (C b) + derivative (chartPoint φ i ρ) v (C a) = _
    simp [derivative]

/-- The difference of two lifts of the same deformation on the same actual
chart is the intrinsic tangent derivation with their coordinate differences. -/
def overlapDerivation (v w : Fin 4 → chart φ i)
    (h : derivative (chartMap φ i).toRingHom v (F φ i) =
      derivative (chartMap φ i).toRingHom w (F φ i)) :
    Derivation K (chart φ i) (chart φ i) :=
  (CycleQ2HodgeEulerChartDerivations.derivationEquiv (F φ i)).symm ⟨v - w, by
    rw [LinearMap.mem_ker, CycleQ2HodgeEulerChartDerivations.gradient_apply]
    change ∑ j, chartMap φ i (pderiv j (F φ i)) * (v j - w j) = 0
    simp only [mul_sub, Finset.sum_sub_distrib]
    apply sub_eq_zero.mpr
    change (∑ j, v j * chartMap φ i (pderiv j (F φ i))) =
      ∑ j, w j * chartMap φ i (pderiv j (F φ i)) at h
    simpa only [mul_comm] using h⟩

theorem overlapDerivation_X (v w : Fin 4 → chart φ i) (h) (j : Fin 4) :
    overlapDerivation φ i v w h (chartMap φ i (X j)) = v j - w j := by
  change ((CycleQ2HodgeEulerChartDerivations.derivationEquiv (F φ i))
    ((CycleQ2HodgeEulerChartDerivations.derivationEquiv (F φ i)).symm _)).val j = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

end CycleQ2HodgeKSChartPoints
end

#print axioms CycleQ2HodgeKSChartPoints.factor_iff
#print axioms CycleQ2HodgeKSChartPoints.deformationPoint_coordinates
#print axioms CycleQ2HodgeKSChartPoints.overlapDerivation_X
