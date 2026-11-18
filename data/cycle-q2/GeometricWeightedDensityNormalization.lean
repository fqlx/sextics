import HodgeComputer.Constructions.HigherResidues.HigherResidue

/-!
# Rescaling the defining equation of a cubic-pole density

Scaling the equation by a nonzero constant scales its first three normal
jets by the same constant. With the numerator jets fixed, the residue
density of the third-order pole scales by the inverse cube. Relative
derivations that annihilate the scalar carry this scaling through the
ordinary divergence of the three primitive coefficients.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2WeightedDensityNormalization

open SplitHigherResidue

variable {K : Type*} [Field K] [CharZero K]

theorem normalDensity_scale (b b₁ b₂ n n₁ n₂ k : K) (hn : n ≠ 0) (hk : k ≠ 0) :
    normalSourceTwo b b₁ b₂ (k * n) (k * n₁) (k * n₂) / (k * n) =
      (k ^ 3)⁻¹ * (normalSourceTwo b b₁ b₂ n n₁ n₂ / n) := by
  unfold normalSourceTwo
  field_simp [hk, hn]

variable {R : Type*} [CommRing R] [Algebra R K]

theorem normalDensity_scale_equation (δ : Derivation R K K) (b G k : K)
    (hG : δ G ≠ 0) (hk : k ≠ 0) (hδ : δ k = 0) :
    normalSourceTwo b (δ b) (δ (δ b)) (δ (k * G)) (δ (δ (k * G)))
        (δ (δ (δ (k * G)))) / δ (k * G) =
      (k ^ 3)⁻¹ * (normalSourceTwo b (δ b) (δ (δ b)) (δ G) (δ (δ G))
        (δ (δ (δ G))) / δ G) := by
  have scale (x : K) : δ (k * x) = k * δ x := by
    rw [Derivation.leibniz, hδ, smul_zero, add_zero, smul_eq_mul]
  simp only [scale]
  exact normalDensity_scale _ _ _ _ _ _ _ hG hk

variable {ι : Type*} [Fintype ι] (D : ι → Derivation R K K)

omit [CharZero K] in
theorem divergence_mul_constant (u : ι → K) (c : K) (hc : ∀ j, D j c = 0) :
    (∑ j, D j (c * u j)) = c * ∑ j, D j (u j) := by
  simp only [Derivation.leibniz, hc, smul_eq_mul, mul_zero, add_zero,
    Finset.mul_sum]

/-- Ordinary relative primitives for the original and scaled equations
determine one another by multiplication by the inverse scaling factors. -/
theorem normalDensity_primitive_iff (b b₁ b₂ n n₁ n₂ k : K)
    (hn : n ≠ 0) (hk : k ≠ 0) (hD : ∀ j, D j k = 0) :
    (∃ u : ι → K, (∑ j, D j (u j)) =
      normalSourceTwo b b₁ b₂ (k * n) (k * n₁) (k * n₂) / (k * n)) ↔
    ∃ u : ι → K, (∑ j, D j (u j)) = normalSourceTwo b b₁ b₂ n n₁ n₂ / n := by
  rw [normalDensity_scale b b₁ b₂ n n₁ n₂ k hn hk]
  have h₃ (j : ι) : D j (k ^ 3) = 0 := by
    simp only [Derivation.leibniz_pow, hD, smul_zero]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨fun j => k ^ 3 * u j, ?_⟩
    rw [divergence_mul_constant D u _ h₃, hu, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hk),
      one_mul]
  · rintro ⟨u, hu⟩
    refine ⟨fun j => (k ^ 3)⁻¹ * u j, ?_⟩
    rw [divergence_mul_constant D u _ (fun j => by
      rw [Derivation.leibniz_inv, h₃, smul_zero]), hu]

end CycleQ2WeightedDensityNormalization

end

#print axioms CycleQ2WeightedDensityNormalization.normalDensity_scale
#print axioms CycleQ2WeightedDensityNormalization.normalDensity_primitive_iff
