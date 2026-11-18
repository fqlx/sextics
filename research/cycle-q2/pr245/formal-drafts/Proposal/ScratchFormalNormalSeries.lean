import Mathlib.RingTheory.LaurentSeries
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import HodgeComputer.Constructions.HigherResidues.HigherResidue

/-!
# Laurent residue of a third-order pole in a transverse coordinate

If the local equation expands as `X * U` with invertible linear
coefficient, the residue of `A / (X * U)^3` uses precisely three
coefficients of the numerator and of the unit. The normalized jet formula
computes the coefficient of exponent minus one in the Laurent series.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2FormalNormalSeries

open PowerSeries
open scoped LaurentSeries
variable {K : Type*} [Field K]

private theorem coeff_two_mul (P Q : PowerSeries K) :
    coeff 2 (P * Q) = constantCoeff P * coeff 2 Q + coeff 1 P * coeff 1 Q +
      coeff 2 P * constantCoeff Q := by
  have h : Finset.HasAntidiagonal.antidiagonal (2 : ℕ) = {(0, 2), (1, 1), (2, 0)} := by decide
  rw [coeff_mul, h]
  simp [coeff_zero_eq_constantCoeff_apply, add_assoc]

private theorem coeff_two_cube (U : PowerSeries K) :
    coeff 2 (U ^ 3) = 3 * coeff 2 U * constantCoeff U ^ 2 +
      3 * coeff 1 U ^ 2 * constantCoeff U := by
  rw [pow_succ, pow_two]
  simp only [coeff_two_mul, coeff_one_mul, map_mul]
  ring

/-- Multiplication by the cube of the power series inverse is division by
the cube on the locus where the constant term is invertible. -/
theorem coeff_two_div_cube (A U : PowerSeries K) (hg : constantCoeff U ≠ 0) :
    coeff 2 (A * U⁻¹ ^ 3) =
      coeff 2 A / constantCoeff U ^ 3 -
      3 * coeff 1 A * coeff 1 U / constantCoeff U ^ 4 +
      constantCoeff A * (6 * coeff 1 U ^ 2 / constantCoeff U ^ 5 -
        3 * coeff 2 U / constantCoeff U ^ 4) := by
  let Q := A * U⁻¹ ^ 3
  have h : Q * U ^ 3 = A := by
    rw [show Q = A * U⁻¹ ^ 3 from rfl, mul_assoc, ← mul_pow,
      PowerSeries.inv_mul_cancel U hg, one_pow, mul_one]
  have h₀ := congrArg (constantCoeff (R := K)) h
  have h₁ := congrArg (coeff (R := K) 1) h
  have h₂ := congrArg (coeff (R := K) 2) h
  simp only [map_mul, map_pow] at h₀
  simp only [coeff_one_mul, coeff_one_pow, map_pow] at h₁
  simp only [coeff_two_mul, coeff_two_cube, coeff_one_pow, map_pow] at h₂
  change coeff 2 Q = _
  apply mul_left_cancel₀ (pow_ne_zero 5 hg)
  calc
    _ = (constantCoeff U)^2 * coeff 2 A -
        3 * coeff 1 U * constantCoeff U * coeff 1 A +
        (6 * (coeff 1 U)^2 - 3 * coeff 2 U * constantCoeff U) * constantCoeff A := by
      linear_combination (constantCoeff U)^2 * h₂ -
        3 * coeff 1 U * constantCoeff U * h₁ +
        (6 * (coeff 1 U)^2 - 3 * coeff 2 U * constantCoeff U) * h₀
    _ = _ := by field_simp [hg]

/-- Actual meromorphic coefficient in the field of formal Laurent series. -/
def cubicPole (A U : PowerSeries K) : LaurentSeries K :=
  (A : LaurentSeries K) / ((PowerSeries.X * U : PowerSeries K) : LaurentSeries K)^3

theorem cubicPole_residue (A U : PowerSeries K) (hg : constantCoeff U ≠ 0) :
    (cubicPole A U).coeff (-1) = coeff 2 (A * U⁻¹ ^ 3) := by
  let e := HahnSeries.ofPowerSeries ℤ K
  let t : LaurentSeries K := HahnSeries.single 1 1
  let s : LaurentSeries K := HahnSeries.single (-3) 1
  have hst : s * t ^ 3 = 1 := by
    dsimp [s, t]
    rw [HahnSeries.single_pow, HahnSeries.single_mul_single]
    norm_num
  have hcancel : e (U⁻¹) ^ 3 * e U ^ 3 = 1 := by
    rw [← mul_pow, ← map_mul, PowerSeries.inv_mul_cancel U hg, map_one, one_pow]
  have hd : (t * e U) ^ 3 ≠ 0 := by
    rw [mul_pow]
    exact mul_ne_zero (right_ne_zero_of_mul_eq_one hst) (right_ne_zero_of_mul_eq_one hcancel)
  have hex : cubicPole A U = s * e (A * U⁻¹ ^ 3) := by
    change e A / (e (PowerSeries.X * U))^3 = _
    rw [map_mul, show e PowerSeries.X = t from HahnSeries.ofPowerSeries_X]
    apply (div_eq_iff hd).mpr
    rw [map_mul, map_pow, mul_pow]
    calc
      e A = (s * t ^ 3) * e A * (e (U⁻¹) ^ 3 * e U ^ 3) := by rw [hst, hcancel, one_mul, mul_one]
      _ = _ := by ring
  rw [hex]
  change (HahnSeries.single (-3) 1 * ((A * U⁻¹ ^ 3 : PowerSeries K) : LaurentSeries K)).coeff (-1) = _
  rw [HahnSeries.coeff_single_mul, one_mul, PowerSeries.coeff_coe]
  norm_num

theorem cubicPole_residue_eq_normalSourceTwo [CharZero K] (A U : PowerSeries K)
    (hg : constantCoeff U ≠ 0) :
    (cubicPole A U).coeff (-1) =
      SplitHigherResidue.normalSourceTwo (constantCoeff A) (coeff 1 A) (2 * coeff 2 A)
        (constantCoeff U) (2 * coeff 1 U) (6 * coeff 2 U) / constantCoeff U := by
  rw [cubicPole_residue A U hg, coeff_two_div_cube A U hg]
  unfold SplitHigherResidue.normalSourceTwo
  field_simp [hg]
  ring

end CycleQ2FormalNormalSeries
end

#print axioms CycleQ2FormalNormalSeries.coeff_two_div_cube
#print axioms CycleQ2FormalNormalSeries.cubicPole_residue_eq_normalSourceTwo
