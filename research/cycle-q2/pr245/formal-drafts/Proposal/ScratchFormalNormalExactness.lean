import Mathlib.RingTheory.LaurentSeries
import Proposal.GeometricFormalInputs03Part02

/-!
# Residues and exactness in the completed transverse coordinate

Extracting exponent minus one sends a top-form divergence in the formal
coordinate and any finite set of tangential coordinates to a tangential
divergence in the coefficient field. Conversely, every other Laurent
coefficient has a characteristic-zero antiderivative. The local exactness
criterion permits poles in all primitive coefficients.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2FormalNormalExactness

variable {K : Type*} [Field K] [CharZero K]

/-- The constant of integration is zero, and the logarithmic term is omitted. -/
def integrate (s : LaurentSeries K) : LaurentSeries K :=
  HahnSeries.ofSuppBddBelow (fun n : ℤ => s.coeff (n - 1) / (n : K)) (by
    refine ⟨s.order + 1, ?_⟩
    intro n hn
    change s.coeff (n - 1) / (n : K) ≠ 0 at hn
    have h : s.coeff (n - 1) ≠ 0 := by
      intro hz
      exact hn (by rw [hz, zero_div])
    have he := HahnSeries.order_le_of_coeff_ne_zero h
    omega)

theorem derivative_coeff (s : LaurentSeries K) (n : ℤ) :
    (LaurentSeries.derivative K s).coeff n = ((n + 1 : ℤ) : K) * s.coeff (n + 1) := by
  rw [LaurentSeries.derivative_apply, LaurentSeries.hasseDeriv_coeff, Ring.choose_one_right]
  simp [zsmul_eq_mul]

theorem derivative_residue (s : LaurentSeries K) :
    (LaurentSeries.derivative K s).coeff (-1) = 0 := by
  rw [derivative_coeff]
  norm_num

theorem derivative_integrate (s : LaurentSeries K) :
    LaurentSeries.derivative K (integrate s) = s - HahnSeries.single (-1) (s.coeff (-1)) := by
  ext n
  rw [derivative_coeff, HahnSeries.coeff_sub, HahnSeries.coeff_single]
  change ((n + 1 : ℤ) : K) * (s.coeff (n + 1 - 1) / ((n + 1 : ℤ) : K)) = _
  by_cases hn : n = -1
  · subst n
    norm_num
  · have hh : (n + 1 : ℤ) ≠ 0 := by omega
    have hK : ((n + 1 : ℤ) : K) ≠ 0 := by exact_mod_cast hh
    rw [if_neg hn, sub_zero, add_sub_cancel_right]
    field_simp [hK]

variable {C ι : Type*} [CommRing C] [Algebra C K] [Fintype ι]

/-- The exact top-form equation in a formally transverse coordinate and
tangential derivations is equivalent to the rational residue equation. -/
theorem divergence_iff_residue (D : ι → Derivation C K K) (s : LaurentSeries K) :
    (∃ t : LaurentSeries K, ∃ v : ι → LaurentSeries K,
      LaurentSeries.derivative K t + ∑ i, CycleQ2LaurentDerivation.extend (D i) (v i) = s) ↔
    ∃ u : ι → K, ∑ i, D i (u i) = s.coeff (-1) := by
  constructor
  · rintro ⟨t, v, he⟩
    refine ⟨fun i => (v i).coeff (-1), ?_⟩
    have hc := congrArg (fun r : LaurentSeries K => r.coeff (-1)) he
    simpa only [HahnSeries.coeff_add, derivative_residue, zero_add, HahnSeries.coeff_sum,
      CycleQ2LaurentDerivation.extend_coeff] using hc
  · rintro ⟨u, hu⟩
    refine ⟨integrate s, fun i => HahnSeries.single (-1) (u i), ?_⟩
    rw [derivative_integrate]
    simp_rw [CycleQ2LaurentDerivation.extend_single]
    change s - HahnSeries.single (-1) (s.coeff (-1)) +
      ∑ i, HahnSeries.single.addMonoidHom (-1) (D i (u i)) = s
    rw [← map_sum, hu]
    exact sub_add_cancel _ _

end CycleQ2FormalNormalExactness
end

#print axioms CycleQ2FormalNormalExactness.derivative_integrate
#print axioms CycleQ2FormalNormalExactness.divergence_iff_residue
