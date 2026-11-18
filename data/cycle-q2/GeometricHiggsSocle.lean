import Proposal.SolutionSupport02Part02
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# A polynomial socle functional for the universal weighted sextic

In degree 18 and character 2 the only Fermat-standard monomial is the socle.
For each other monomial choose a dividing Fermat gradient monomial. The
corresponding actual gradient multiples, normalized by their nonzero Fermat
leading scalars, give a square coefficient matrix after adjoining the socle
column. Its specialization is the identity. The socle row of its adjugate
evaluates triple products over the original coefficient ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 6000

noncomputable section
namespace CycleQ2HiggsSocle

open MvPolynomial CycleQ2FermatHiggs CycleQ2FermatJacobian CycleQ2GenericSexticGradient

abbrev Row := {a : Fin 5 → Fin 19 //
  weightedDegree (fun i => (a i).val) = 18 ∧ character (fun i => (a i).val) = 2}

/-- The determinant only uses the finite indexing type abstractly. -/
noncomputable instance instFintypeRow : Fintype Row := Fintype.ofFinite Row

def exp (d : Row) : Exp := exponent (fun i => (d.val i).val)

theorem exp_injective : Function.Injective exp := by
  intro d e h
  apply Subtype.ext
  funext i
  apply Fin.ext
  exact congrArg (fun z : Exp => z i) h

def rowOfExp (a : Exp) (hd : weightedDegree a = 18) (hc : character a = 2) : Row := by
  have hb (i : Fin 5) : a i < 19 := by
    have hh : a 0 + a 1 + a 2 + a 3 + 2 * a 4 = 18 := hd
    fin_cases i
    · change a 0 < 19
      omega
    · change a 1 < 19
      omega
    · change a 2 < 19
      omega
    · change a 3 < 19
      omega
    · change a 4 < 19
      omega
  exact ⟨fun i => ⟨a i, hb i⟩, hd, hc⟩

@[simp] theorem exp_rowOfExp (a : Exp) (hd : weightedDegree a = 18) (hc : character a = 2) :
    exp (rowOfExp a hd hc) = a := by ext i; rfl

def topRow : Row :=
  ⟨fun i => ⟨socle i, by fin_cases i <;> decide⟩, socle_weightedDegree_character⟩

@[simp] theorem exp_topRow : exp topRow = exponent socle := rfl

theorem exceeding (d : Row) (h : d ≠ topRow) : ∃ i : Fin 5, cutoff i ≤ exp d i := by
  by_contra! hn
  apply h
  apply exp_injective
  ext i
  have h0 := hn 0
  have h1 := hn 1
  have h2 := hn 2
  have h3 := hn 3
  have h4 := hn 4
  have hd := d.property.1
  change (d.val 0).val + (d.val 1).val + (d.val 2).val + (d.val 3).val + 2 * (d.val 4).val = 18 at hd
  change (d.val 0).val < 5 at h0
  change (d.val 1).val < 5 at h1
  change (d.val 2).val < 5 at h2
  change (d.val 3).val < 5 at h3
  change (d.val 4).val < 2 at h4
  fin_cases i
  · change (d.val 0).val = 4
    omega
  · change (d.val 1).val = 4
    omega
  · change (d.val 2).val = 4
    omega
  · change (d.val 3).val = 4
    omega
  · change (d.val 4).val = 1
    omega

def chosen (d : Row) (h : d ≠ topRow) : Fin 5 := Classical.choose (exceeding d h)

theorem chosen_le (d : Row) (h : d ≠ topRow) : cutoff (chosen d h) ≤ exp d (chosen d h) :=
  Classical.choose_spec (exceeding d h)

abbrev FamilyPoly := MvPolynomial (Fin 5) CoeffRing

def multiple (d : Row) (i : Fin 5) : FamilyPoly :=
  monomial (exp d - Finsupp.single i (cutoff i)) 1 * pderiv i universalF

def column (d : Row) : FamilyPoly :=
  if h : d = topRow then monomial (exp topRow) 1
  else (C ((derivativeScalar (chosen d h))⁻¹) : CoeffRing) • multiple d (chosen d h)

def coefficients (R : Type*) [CommRing R] : MvPolynomial (Fin 5) R →ₗ[R] (Row → R) :=
  LinearMap.pi (fun d => lcoeff R (exp d))

def macaulay : Matrix Row Row CoeffRing := Matrix.of fun d e => coeff (exp d) (column e)

theorem multiple_seed (d : Row) (i : Fin 5) (hi : cutoff i ≤ exp d i) :
    MvPolynomial.map seedEvaluation (multiple d i) = monomial (exp d) (derivativeScalar i) := by
  have hle : Finsupp.single i (cutoff i) ≤ exp d := Finsupp.single_le_iff.mpr hi
  rw [multiple, map_mul, ← pderiv_map, universalF_seed, derivative_eq,
    generator, X_pow_eq_monomial, C_mul_monomial, map_monomial, map_one, monomial_mul,
    tsub_add_cancel_of_le hle, mul_one, one_mul]

theorem column_seed (d : Row) :
    MvPolynomial.map seedEvaluation (column d) = monomial (exp d) 1 := by
  classical
  by_cases h : d = topRow
  · subst d
    simp [column]
  · rw [column, dif_neg h, smul_eq_C_mul, map_mul, map_C, multiple_seed d _ (chosen_le d h)]
    simp [CycleQ2GenericSexticGradient.seedEvaluation, C_mul_monomial, derivativeScalar_ne_zero]

theorem macaulay_seed : macaulay.map seedEvaluation = (1 : Matrix Row Row ℂ) := by
  classical
  ext d e
  change seedEvaluation (coeff (exp d) (column e)) = _
  rw [← coeff_map, column_seed, coeff_monomial, Matrix.one_apply]
  by_cases h : d = e
  · simp [h]
  · rw [if_neg (fun he : exp e = exp d => h (exp_injective he.symm)), if_neg h]

theorem det_seed : seedEvaluation macaulay.det = 1 := by
  rw [RingHom.map_det]
  change (macaulay.map seedEvaluation).det = 1
  rw [macaulay_seed, Matrix.det_one]

section Cramer

variable {I V A B : Type*} [Fintype I] [DecidableEq I] [CommRing A] [CommRing B]
  [AddCommGroup V] [Module A V]

private def cramerRow (M : Matrix I I A) (v : V →ₗ[A] (I → A)) (k : I) : V →ₗ[A] A :=
  (LinearMap.proj k).comp (M.cramer.comp v)

private theorem cramerRow_apply (M : Matrix I I A) (v : V →ₗ[A] (I → A)) (k : I) (p : V) :
    cramerRow M v k p = M.cramer (v p) k := rfl

private theorem cramerRow_column (M : Matrix I I A) (v : V →ₗ[A] (I → A)) (k j : I) (p : V)
    (hp : ∀ e, v p e = M e j) : cramerRow M v k p = (Pi.single j M.det : I → A) k :=
  congrFun (Matrix.cramer_row_self M (v p) j hp) k

private theorem cramerRow_one (v : V →ₗ[A] (I → A)) (k : I) (p : V) :
    cramerRow 1 v k p = v p k := by
  rw [cramerRow_apply, Matrix.cramer_one]
  rfl

private theorem map_cramer (f : A →+* B) (M : Matrix I I A) (b : I → A) (k : I) :
    f (M.cramer b k) = (M.map f).cramer (f ∘ b) k := by
  rw [Matrix.cramer_apply, Matrix.cramer_apply, RingHom.map_det]
  exact congrArg Matrix.det (Matrix.map_updateCol (M := M) (j := k) (c := b) f)

end Cramer

def traceAt {K : Type*} [CommRing K] (f : CoeffRing →+* K) :
    MvPolynomial (Fin 5) K →ₗ[K] K :=
  cramerRow (macaulay.map f) (coefficients K) topRow

def trace : FamilyPoly →ₗ[CoeffRing] CoeffRing :=
  cramerRow macaulay (coefficients CoeffRing) topRow

theorem traceAt_congr {K : Type*} [CommRing K] (f : CoeffRing →+* K)
    {p q : MvPolynomial (Fin 5) K} (h : coefficients K p = coefficients K q) :
    traceAt f p = traceAt f q := by
  rw [traceAt, cramerRow_apply, cramerRow_apply, h]

theorem map_trace {K : Type*} [CommRing K] (f : CoeffRing →+* K) (p : FamilyPoly) :
    f (trace p) = traceAt f (MvPolynomial.map f p) := by
  rw [trace, traceAt, cramerRow_apply, cramerRow_apply, map_cramer]
  apply congrArg (fun b => (macaulay.map f).cramer b topRow)
  funext d
  exact (coeff_map f p (exp d)).symm

theorem map_multiple {K : Type*} [CommRing K] (f : CoeffRing →+* K) (d : Row) (i : Fin 5) :
    MvPolynomial.map f (multiple d i) =
      monomial (exp d - Finsupp.single i (cutoff i)) 1 * pderiv i (MvPolynomial.map f universalF) := by
  simp only [multiple, map_mul, map_monomial, map_one, pderiv_map]

theorem traceAt_multiple {K : Type*} [CommRing K] (f : CoeffRing →+* K) (d : Row) (i : Fin 5) :
    traceAt f (monomial (exp d - Finsupp.single i (cutoff i)) 1 *
      pderiv i (MvPolynomial.map f universalF)) = f (trace (multiple d i)) := by
  rw [map_trace, map_multiple]

theorem seed_trace (p : FamilyPoly) :
    seedEvaluation (trace p) = coeff (exponent socle) (MvPolynomial.map seedEvaluation p) := by
  rw [map_trace, traceAt, macaulay_seed, cramerRow_one]
  rfl

theorem trace_column (d : Row) :
    trace (column d) = (Pi.single d macaulay.det : Row → CoeffRing) topRow :=
  cramerRow_column macaulay (coefficients CoeffRing) topRow d (column d) (fun _ => rfl)

theorem trace_chosen (d : Row) (h : d ≠ topRow) : trace (multiple d (chosen d h)) = 0 := by
  have hh := trace_column d
  rw [column, dif_neg h, map_smul, smul_eq_mul, Pi.single_eq_of_ne h.symm] at hh
  exact (mul_eq_zero.mp hh).resolve_left (C_ne_zero.mpr (inv_ne_zero (derivativeScalar_ne_zero _)))

theorem trace_socle : trace (monomial (exponent socle) 1) = macaulay.det := by
  simpa [column] using trace_column topRow

def triple (R : Type*) [CommRing R] (m : Fin 35) (i j : Fin 33) : MvPolynomial (Fin 5) R :=
  monomial (exponent (basisMonomial i)) 1 * monomial (exponent (basisMonomial j)) 1 *
    monomial (exponent (tangentMonomial m)) 1

def H (m : Fin 35) : Matrix (Fin 33) (Fin 33) CoeffRing :=
  Matrix.of fun i j => trace (triple CoeffRing m i j)

theorem H_seed (m : Fin 35) : (H m).map seedEvaluation = higgsMatrix ℂ m := by
  ext i j
  have h := seed_trace (triple CoeffRing m i j)
  apply h.trans
  simp only [triple, map_mul, map_monomial, map_one]
  simpa only [monomialClass, ← map_mul, socleTrace_mk] using
    socleTrace_triple_eq_higgsMatrix m i j

end CycleQ2HiggsSocle
end

#print axioms CycleQ2HiggsSocle.trace_chosen
#print axioms CycleQ2HiggsSocle.det_seed
#print axioms CycleQ2HiggsSocle.H_seed
