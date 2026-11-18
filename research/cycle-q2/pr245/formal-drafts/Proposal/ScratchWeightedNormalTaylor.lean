import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.Algebra.Polynomial.Derivative
import Mathlib.Algebra.Polynomial.Inductions
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2WeightedNormalTaylor
open MvPolynomial
variable {A K : Type*} [CommRing A] [Field K]
abbrev Pol (A : Type*) [CommRing A] := MvPolynomial (Fin 4) A

/-- Translate the eliminated coordinate at a point of the hypersurface.
The other three coordinates remain fixed. -/
def translate (v : Pol A →+* K) : Pol A →+* Polynomial K :=
  eval₂Hom (Polynomial.C.comp (v.comp MvPolynomial.C)) fun j =>
    if j = 0 then Polynomial.C (v (X j)) + Polynomial.X else Polynomial.C (v (X j))

theorem translate_coeff_zero (v : Pol A →+* K) (q : Pol A) :
    (translate v q).coeff 0 = v q := by
  rw [Polynomial.coeff_zero_eq_eval_zero]
  induction q using MvPolynomial.induction_on with
  | C a => simp [translate]
  | add p q hp hq => simp only [map_add, Polynomial.eval_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, Polynomial.eval_mul, hp]
    congr 1
    by_cases hj : j = 0 <;> simp [translate, hj]

theorem derivative_translate (v : Pol A →+* K) (q : Pol A) :
    (translate v q).derivative = translate v (pderiv 0 q) := by
  induction q using MvPolynomial.induction_on with
  | C a => simp [translate]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, Polynomial.derivative_mul, pderiv_mul, map_add, hp]
    by_cases hj : j = 0
    · subst j
      simp [translate]
    · simp [translate, hj, pderiv_X_of_ne hj]

theorem translate_coeff_one (v : Pol A →+* K) (q : Pol A) :
    (translate v q).coeff 1 = v (pderiv 0 q) := by
  have h := translate_coeff_zero v (pderiv 0 q)
  rw [← derivative_translate, Polynomial.coeff_derivative] at h
  simpa using h

variable [CharZero K]

theorem translate_coeff_two (v : Pol A →+* K) (q : Pol A) :
    (translate v q).coeff 2 = v (pderiv 0 (pderiv 0 q)) / 2 := by
  apply (eq_div_iff (by norm_num : (2 : K) ≠ 0)).2
  have h := translate_coeff_one v (pderiv 0 q)
  rw [← derivative_translate, Polynomial.coeff_derivative] at h
  norm_num at h
  exact h

theorem translate_coeff_three (v : Pol A →+* K) (q : Pol A) :
    (translate v q).coeff 3 = v (pderiv 0 (pderiv 0 (pderiv 0 q))) / 6 := by
  have h := translate_coeff_two v (pderiv 0 q)
  rw [← derivative_translate, Polynomial.coeff_derivative] at h
  norm_num at h
  have e := (eq_div_iff (by norm_num : (2 : K) ≠ 0)).mp h
  apply (eq_div_iff (by norm_num : (6 : K) ≠ 0)).mpr
  rw [← e]
  ring

omit [CharZero K] in
/-- On the hypersurface the translated denominator splits as the parameter
times a polynomial whose constant term is the normal Jacobian. -/
theorem translate_equation (v : Pol A →+* K) (f : Pol A) (hf : v f = 0) :
    translate v f = Polynomial.X * (translate v f).divX := by
  simpa only [translate_coeff_zero, hf, Polynomial.C_0, add_zero] using
    (Polynomial.X_mul_divX_add (translate v f)).symm

theorem normal_unit_jets (v : Pol A →+* K) (f : Pol A) :
    ((translate v f).divX.coeff 0 = v (pderiv 0 f)) ∧
    ((translate v f).divX.coeff 1 = v (pderiv 0 (pderiv 0 f)) / 2) ∧
    ((translate v f).divX.coeff 2 = v (pderiv 0 (pderiv 0 (pderiv 0 f))) / 6) := by
  simp only [Polynomial.coeff_divX]
  exact ⟨translate_coeff_one v f, translate_coeff_two v f, translate_coeff_three v f⟩
end CycleQ2WeightedNormalTaylor
#print axioms CycleQ2WeightedNormalTaylor.normal_unit_jets
