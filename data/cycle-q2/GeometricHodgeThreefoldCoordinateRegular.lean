import Proposal.GeometricHodgeThreefold
import Mathlib.Algebra.Regular.Basic

/-!
# The weight-one coordinates act injectively on the sextic cone

Over an integral domain, none of the original weight-one variables divides
the sextic when the coefficient of the pure weight-two cube is nonzero.
Primality and cancellation of the variable in the polynomial ring therefore
give regularity in the homogeneous quotient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2GeometricHodgeThreefold

open MvPolynomial CycleQ2IncidenceNormalForm
open CycleQ2GenericSexticGradient (CoeffRing universalF)

variable {R : Type} [CommRing R] [IsDomain R] (φ : CoeffRing →+* R)

theorem equation_leading :
    (equation φ).coeff (Finsupp.single 4 3) = φ vertexCoefficient := by
  rw [← fullSexticLeadingIndex_exponent, equation, universalF, map_fullInvariantPolynomial,
    fullInvariantPolynomial_coeff]
  rfl

theorem coordinate_not_dvd_equation (h : φ vertexCoefficient ≠ 0) (i : Fin 4) :
    ¬ X i.castSucc ∣ equation φ := by
  rintro ⟨q, hq⟩
  apply h
  rw [← equation_leading φ, hq, coeff_X_mul', if_neg]
  simpa only [Finsupp.mem_support_iff, not_not] using
    (Finsupp.single_eq_of_ne (Fin.castSucc_ne_last i) : (Finsupp.single (4 : Fin 5) (3 : ℕ)) i.castSucc = 0)

theorem coord_isRegular (h : IsUnit (φ vertexCoefficient)) (i : Fin 4) :
    IsRegular (coord φ i.castSucc) := by
  apply (Commute.isRegular_iff (fun b => Commute.all _ b)).mpr
  apply isLeftRegular_iff_right_eq_zero_of_mul.mpr
  intro z hz
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective z
  change quotient φ (X i.castSucc) * quotient φ p = 0 at hz
  rw [← map_mul] at hz
  obtain ⟨q, hq⟩ := Ideal.mem_span_singleton.mp (Ideal.Quotient.eq_zero_iff_mem.mp hz)
  have hd : X i.castSucc ∣ equation φ * q := ⟨p, hq.symm⟩
  obtain ⟨b, rfl⟩ := (X_dvd_mul_iff.mp hd).resolve_left (coordinate_not_dvd_equation φ h.ne_zero i)
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  apply Ideal.mem_span_singleton.mpr
  exact ⟨b, mul_left_cancel₀ (X_ne_zero i.castSucc) (by simpa only [mul_left_comm] using hq)⟩

end CycleQ2GeometricHodgeThreefold
end

#print axioms CycleQ2GeometricHodgeThreefold.coord_isRegular
