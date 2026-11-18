import Proposal.ScratchFormalNormalExactness

/-!
# Ambient partial derivatives in a translated normal chart

Translating one ambient coordinate by a residue-field function changes
the spatial partial derivatives by a normal derivative. The latter
integrates to zero under the residue. We construct the actual Laurent
derivations and prove the divergence criterion also for these partials.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace CycleQ2FormalNormalPartials

open CycleQ2FormalNormalExactness
variable {K : Type*} [Field K] [CharZero K]

local instance coefficientAlgebra : Algebra ℤ (LaurentSeries K) := HahnSeries.instAlgebra

private def euler (x : LaurentSeries K) : LaurentSeries K where
  coeff n := (n : K) * x.coeff n
  isPWO_support' := x.isPWO_support.mono (by
    intro n hn hz
    exact hn (by simp only [hz, mul_zero]))

private theorem support_euler (x : LaurentSeries K) : (euler x).support ⊆ x.support := by
  intro n hn hz
  exact hn (by change (n : K) * x.coeff n = 0; rw [hz, mul_zero])

private theorem euler_mul (x y : LaurentSeries K) : euler (x * y) =
    euler x * y + x * euler y := by
  ext n
  change (n : K) * (x * y).coeff n = _
  rw [HahnSeries.coeff_mul, HahnSeries.coeff_add,
    HahnSeries.coeff_mul_left' x.isPWO_support (support_euler x),
    HahnSeries.coeff_mul_right' y.isPWO_support (support_euler y),
    Finset.mul_sum, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  have hn : p.1 + p.2 = n := (Finset.mem_antidiagonal.mp hp).2.2
  change (n : K) * (x.coeff p.1 * y.coeff p.2) =
    ((p.1 : K) * x.coeff p.1) * y.coeff p.2 +
      x.coeff p.1 * ((p.2 : K) * y.coeff p.2)
  rw [← hn, Int.cast_add]
  ring

private theorem derivative_eq (x : LaurentSeries K) :
    LaurentSeries.derivative K x = HahnSeries.single (-1) 1 * euler x := by
  ext n
  rw [derivative_coeff, HahnSeries.coeff_single_mul, one_mul, sub_neg_eq_add]
  rfl

/-- Derivation in the formal parameter, bundled with its genuine Leibniz law. -/
def normal : Derivation ℤ (LaurentSeries K) (LaurentSeries K) where
  toFun := LaurentSeries.derivative K
  map_add' := (LaurentSeries.derivative K).map_add
  map_smul' r s := by
    ext n
    simp only [derivative_coeff, HahnSeries.coeff_smul, RingHom.id_apply]
    simp only [zsmul_eq_mul]
    ring
  map_one_eq_zero' := by
    ext n
    rw [derivative_coeff, HahnSeries.coeff_one, HahnSeries.coeff_zero]
    split_ifs with h
    · rw [h, Int.cast_zero, zero_mul]
    · rw [mul_zero]
  leibniz' := by
    intro a b
    change LaurentSeries.derivative K (a * b) =
      a * LaurentSeries.derivative K b + b * LaurentSeries.derivative K a
    rw [derivative_eq, derivative_eq, derivative_eq, euler_mul]
    ring

theorem normal_apply (s : LaurentSeries K) :
    normal s = LaurentSeries.derivative K s := rfl

theorem normal_C (a : K) : normal (HahnSeries.single (0 : ℤ) a) = 0 := by
  ext n
  rw [normal_apply, derivative_coeff, HahnSeries.coeff_single, HahnSeries.coeff_zero]
  split_ifs with h
  · rw [h, Int.cast_zero, zero_mul]
  · rw [mul_zero]

theorem normal_t : normal (HahnSeries.single (1 : ℤ) (1 : K)) = 1 := by
  ext n
  rw [normal_apply, derivative_coeff, HahnSeries.coeff_single, HahnSeries.coeff_one]
  by_cases h : n = 0
  · subst n
    norm_num
  · have h₁ : n + 1 ≠ 1 := by omega
    simp [h₁, h]

/-- Partial derivative with respect to a spatial coordinate at fixed
original ambient normal coordinate. -/
def spatial (D : Derivation ℤ K K) (z : K) :
    Derivation ℤ (LaurentSeries K) (LaurentSeries K) :=
  CycleQ2LaurentDerivation.extend D - HahnSeries.single 0 (D z) • normal (K := K)

theorem spatial_C (D : Derivation ℤ K K) (z a : K) :
    spatial D z (HahnSeries.single (0 : ℤ) a) = HahnSeries.single 0 (D a) := by
  simp [spatial, Derivation.sub_apply, Derivation.smul_apply,
    CycleQ2LaurentDerivation.extend_single, normal_C]

theorem spatial_t (D : Derivation ℤ K K) (z : K) :
    spatial D z (HahnSeries.single (1 : ℤ) 1) = -HahnSeries.single 0 (D z) := by
  simp [spatial, Derivation.sub_apply, Derivation.smul_apply, CycleQ2LaurentDerivation.extend_single,
    normal_t, smul_eq_mul]

theorem spatial_residue (D : Derivation ℤ K K) (z : K) (s : LaurentSeries K) :
    (spatial D z s).coeff (-1) = D (s.coeff (-1)) := by
  change (CycleQ2LaurentDerivation.extend D s -
    HahnSeries.single 0 (D z) * LaurentSeries.derivative K s).coeff (-1) = _
  rw [HahnSeries.coeff_sub, CycleQ2LaurentDerivation.extend_coeff,
    HahnSeries.coeff_single_mul, sub_zero, derivative_residue, mul_zero, sub_zero]

/-- A meromorphic ambient divergence gives a tangential primitive after
taking residues in the translated transverse variable. -/
theorem residue_of_ambient_divergence {ι : Type*} [Fintype ι]
    (D : ι → Derivation ℤ K K) (z : K) (a t : LaurentSeries K)
    (v : ι → LaurentSeries K)
    (he : normal t + ∑ i, spatial (D i) z (v i) = a) :
    ∑ i, D i ((v i).coeff (-1)) = a.coeff (-1) := by
  have h := congrArg (fun s : LaurentSeries K => s.coeff (-1)) he
  simpa only [HahnSeries.coeff_add, normal_apply, derivative_residue, zero_add,
    HahnSeries.coeff_sum, spatial_residue] using h

end CycleQ2FormalNormalPartials
end

#print axioms CycleQ2FormalNormalPartials.normal
#print axioms CycleQ2FormalNormalPartials.residue_of_ambient_divergence
