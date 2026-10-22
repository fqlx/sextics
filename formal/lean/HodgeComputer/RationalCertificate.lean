import HodgeComputer.Verify
import HodgeComputer.ResidualCorrections
import Mathlib.RingTheory.Derivation.Basic

/-!
# A rational operator for the full certificate identity

The correction consists of a rational vector field and a rational quotient
term.  The operator is additive for fixed `F`, `q`, and coordinate derivations.
Its translation to `Verify` retains the full quotient, with no normalization
or extra bound on the legal denominator.  The application must supply actual
coordinate derivations and their compatibility with polynomial evaluation.
-/

noncomputable section
namespace HodgeComputer
open HodgeTestbed MvPolynomial
open scoped BigOperators

variable {K : Type*} [Field K]

/-- The source contributed by a rational field and its quotient term.
For a polynomial witness these two inputs are `N/D` and `Q/D²`. -/
def rationalCertificateOperator (Δ : Fin 6 → Derivation ℤ K K)
    (F : K) (q : ℕ) : ((Fin 6 → K) × K) →+ K where
  toFun := fun x =>
    (q : K) * (∑ i, Δ i F * x.1 i) - F * (∑ i, Δ i (x.1 i)) +
      F^(q+1) * x.2
  map_zero' := by simp
  map_add' := by
    intro x y
    change (q : K) * (∑ i, Δ i F * (x.1 i + y.1 i)) -
        F * (∑ i, Δ i (x.1 i + y.1 i)) + F^(q+1) * (x.2 + y.2) = _
    simp only [mul_add, map_add, Finset.sum_add_distrib]
    ring

variable (φ : Poly →+* K) (Δ : Fin 6 → Derivation ℤ K K)
    (compatible : ∀ i p, Δ i (φ p) = φ (pderiv i p))

include compatible

theorem rational_directional (F D : Poly) (N : Fin 6 → Poly) :
    (∑ i, Δ i (φ F) * (φ (N i) / φ D)) = φ (directional F N) / φ D := by
  simp only [compatible, directional, map_sum, map_mul, mul_div_assoc,
    Finset.sum_div]

/-- The product rule includes every derivative of the denominator. -/
theorem rational_divergence (D : Poly) (N : Fin 6 → Poly) :
    (∑ i, Δ i (φ (N i) / φ D)) = φ (divergenceNumerator D N) / (φ D)^2 := by
  calc
    _ = (∑ i, (φ D * φ (pderiv i (N i)) -
        φ (pderiv i D) * φ (N i))) / (φ D)^2 := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i _
      rw [Derivation.leibniz_div, compatible, compatible]
      simp only [smul_eq_mul, div_eq_mul_inv, inv_pow]
      ring
    _ = _ := by
      simp only [divergenceNumerator, divergence, directional, map_sub,
        map_mul, map_sum, Finset.sum_sub_distrib, Finset.mul_sum]

/-- Exact clearing of the rational operator, before degree or legality checks. -/
theorem rationalCertificateOperator_mul_denominator
    (F D Q : Poly) (N : Fin 6 → Poly) (q : ℕ) (hD : φ D ≠ 0) :
    rationalCertificateOperator Δ (φ F) q
        ((fun i => φ (N i) / φ D), φ Q / (φ D)^2) * (φ D)^2 =
      (q : K) * φ D * φ (directional F N) -
        φ F * φ (divergenceNumerator D N) + (φ F)^(q+1) * φ Q := by
  change ((q : K) * (∑ i, Δ i (φ F) * (φ (N i) / φ D)) -
    φ F * (∑ i, Δ i (φ (N i) / φ D)) +
    (φ F)^(q+1) * (φ Q / (φ D)^2)) * (φ D)^2 = _
  rw [rational_directional φ Δ compatible, rational_divergence φ Δ compatible]
  field_simp [hD]

/-- The rational operator identity is equivalent to the original cleared
identity. Injectivity prevents an identity valid only on a slice or modulo
`F` from being used as a certificate on the ambient polynomial ring. -/
theorem rationalCertificateOperator_eq_iff
    (injective : Function.Injective φ)
    (F A D Q : Poly) (N : Fin 6 → Poly) (q : ℕ) (hD : φ D ≠ 0) :
    rationalCertificateOperator Δ (φ F) q
        ((fun i => φ (N i) / φ D), φ Q / (φ D)^2) = φ A ↔
      defect F A D q N = F^(q+1) * Q := by
  have cleared := rationalCertificateOperator_mul_denominator
    φ Δ compatible F D Q N q hD
  constructor
  · intro h
    rw [h] at cleared
    apply injective
    simp only [defect, map_add, map_sub, map_mul, map_pow, map_natCast]
    linear_combination cleared
  · intro h
    have mapped := congrArg φ h
    simp only [defect, map_add, map_sub, map_mul, map_pow, map_natCast] at mapped
    apply mul_right_cancel₀ (pow_ne_zero 2 hD)
    linear_combination cleared - mapped

/-- Return from common rational coordinates to the full certificate contract.
The degree and denominator obligations remain explicit, and `Q` is arbitrary. -/
theorem verify_iff_rationalCertificateOperator
    (injective : Function.Injective φ)
    (F A D Q : Poly) (N : Fin 6 → Poly) (q d : ℕ)
    (hD : D ≠ 0) (homogeneousD : D.IsHomogeneous d)
    (homogeneousN : ∀ i, (N i).IsHomogeneous (d + 6*q - 5))
    (legal : IsRelPrime F D) :
    Verify F A q d D N Q ↔
      rationalCertificateOperator Δ (φ F) q
        ((fun i => φ (N i) / φ D), φ Q / (φ D)^2) = φ A := by
  have hφD : φ D ≠ 0 := by
    intro h
    exact hD (injective (h.trans (map_zero φ).symm))
  have identity := rationalCertificateOperator_eq_iff
    φ Δ compatible injective F A D Q N q hφD
  exact ⟨fun h => identity.mpr h.identity,
    fun h => ⟨hD, homogeneousD, homogeneousN, legal, identity.mp h⟩⟩

/-- Assemble rational corrections first, then return to the original contract
once for their total. Individual remainders need not be polynomial sources.
Common legal homogeneous representatives of the total remain an explicit
obligation, even if the individual formulas use additional fibre poles. -/
theorem hasCertificate_of_rational_corrections
    (injective : Function.Injective φ)
    (F A D Q : Poly) (N : Fin 6 → Poly) (q d n : ℕ)
    (hD : D ≠ 0) (homogeneousD : D.IsHomogeneous d)
    (homogeneousN : ∀ i, (N i).IsHomogeneous (d + 6*q - 5))
    (legal : IsRelPrime F D)
    (R : ℕ → K) (delta : ℕ → ((Fin 6 → K) × K))
    (initial : R 0 = φ A) (final : R n = 0)
    (step : ∀ k < n, rationalCertificateOperator Δ (φ F) q (delta k) =
      R k - R (k + 1))
    (representatives : (∑ k ∈ Finset.range n, delta k) =
      ((fun i => φ (N i) / φ D), φ Q / (φ D)^2)) :
    HasCertificate F A q := by
  refine ⟨d, D, N, Q, (verify_iff_rationalCertificateOperator
    φ Δ compatible injective F A D Q N q d hD homogeneousD homogeneousN legal).mpr ?_⟩
  rw [← representatives]
  exact ResidualCorrections.sum_eq_source
    (rationalCertificateOperator Δ (φ F) q) (φ A) R delta n initial final step

end HodgeComputer
