import Proposal.SolutionSupport02Part02

/-!
# Monomial and Jacobian columns over the full invariant sextic base

For a fixed weighted degree and character, keep every Fermat standard
monomial and replace each remaining monomial by one multiple of a partial
derivative of the universal polynomial. The full square coefficient matrix
specializes to the identity for the literal Fermat coefficients. Its
determinant defines a principal open of the full coefficient space.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HiggsJacobianFrames

open MvPolynomial Matrix CycleQ2IncidenceNormalForm
open CycleQ2GenericSexticGradient (CoeffRing universalF seedEvaluation universalF_seed)
open CycleQ2FermatJacobian (cutoff derivativeScalar derivativeScalar_ne_zero)

abbrev Index (n : ℕ) (χ : ZMod 3) :=
  {e : Fin 5 → Fin (n + 1) // Finsupp.weight fullGrading (fullExponentOf e) = (n, χ)}

def exp {n : ℕ} {χ : ZMod 3} (e : Index n χ) : Fin 5 →₀ ℕ := fullExponentOf e.val

theorem exp_injective {n : ℕ} {χ : ZMod 3} :
    Function.Injective (exp (n := n) (χ := χ)) := by
  intro a b h
  apply Subtype.ext
  funext i
  apply Fin.ext
  simpa only [exp, fullExponentOf_apply] using congrArg (fun x : Fin 5 →₀ ℕ => x i) h

theorem exists_index {n : ℕ} {χ : ZMod 3} (x : Fin 5 →₀ ℕ)
    (hx : Finsupp.weight fullGrading x = (n, χ)) : ∃ e : Index n χ, exp e = x := by
  have hd : fullDegree x = n := congrArg Prod.fst ((fullGrading_weight x).symm.trans hx)
  have hb (i : Fin 5) : x i < n + 1 := by
    unfold fullDegree at hd
    fin_cases i
    · change x 0 < n + 1
      omega
    · change x 1 < n + 1
      omega
    · change x 2 < n + 1
      omega
    · change x 3 < n + 1
      omega
    · change x 4 < n + 1
      omega
  let e (i : Fin 5) : Fin (n + 1) := ⟨x i, hb i⟩
  have he : fullExponentOf e = x := by ext i; exact fullExponentOf_apply e i
  exact ⟨⟨e, he ▸ hx⟩, he⟩

def Standard {n : ℕ} {χ : ZMod 3} (e : Index n χ) : Prop := ∀ i, exp e i < cutoff i

abbrev Bounded (n : ℕ) (χ : ZMod 3) := {e : Index n χ // Standard e}

theorem exists_pivot {n : ℕ} {χ : ZMod 3} {e : Index n χ} (h : ¬ Standard e) :
    ∃ i, Finsupp.single i (cutoff i) ≤ exp e := by
  classical
  unfold Standard at h
  push Not at h
  obtain ⟨i, hi⟩ := h
  exact ⟨i, Finsupp.single_le_iff.mpr hi⟩

def pivot {n : ℕ} {χ : ZMod 3} {e : Index n χ} (h : ¬ Standard e) := (exists_pivot h).choose

theorem pivot_le {n : ℕ} {χ : ZMod 3} {e : Index n χ} (h : ¬ Standard e) :
    Finsupp.single (pivot h) (cutoff (pivot h)) ≤ exp e := (exists_pivot h).choose_spec

def column {n : ℕ} {χ : ZMod 3} (e : Index n χ) : MvPolynomial (Fin 5) CoeffRing := by
  classical
  exact if h : Standard e then monomial (exp e) 1 else
    let i := pivot h
    monomial (exp e - Finsupp.single i (cutoff i)) (C (derivativeScalar i)⁻¹) *
      pderiv i universalF

theorem seed_column {n : ℕ} {χ : ZMod 3} (e : Index n χ) :
    MvPolynomial.map seedEvaluation (column e) = monomial (exp e) (1 : ℂ) := by
  classical
  unfold column
  split_ifs with h
  · simp
  · simp only [map_mul, map_monomial, CycleQ2GenericSexticGradient.seedEvaluation, eval_C,
      ← pderiv_map]
    rw [show MvPolynomial.map (eval CycleQ2GenericSexticGradient.fermatCoefficients) universalF =
          CycleQ2FermatJacobian.fermat from universalF_seed,
      CycleQ2FermatJacobian.derivative_eq, CycleQ2FermatJacobian.generator, X_pow_eq_monomial,
      C_mul_monomial, mul_one, monomial_mul, inv_mul_cancel₀ (derivativeScalar_ne_zero _),
      tsub_add_cancel_of_le (pivot_le h)]

def frameMatrix (n : ℕ) (χ : ZMod 3) : Matrix (Index n χ) (Index n χ) CoeffRing :=
  fun i j => coeff (exp i) (column j)

theorem seed_frameMatrix (n : ℕ) (χ : ZMod 3) :
    (frameMatrix n χ).map seedEvaluation = 1 := by
  classical
  ext i j
  change seedEvaluation (coeff (exp i) (column j)) = (1 : Matrix (Index n χ) _ ℂ) i j
  rw [← coeff_map, seed_column, coeff_monomial, Matrix.one_apply]
  simp [exp_injective.eq_iff, eq_comm]

def frameDet (n : ℕ) (χ : ZMod 3) : CoeffRing := (frameMatrix n χ).det

@[simp] theorem seed_frameDet (n : ℕ) (χ : ZMod 3) : seedEvaluation (frameDet n χ) = 1 := by
  rw [frameDet, RingHom.map_det]
  change ((frameMatrix n χ).map seedEvaluation).det = 1
  rw [seed_frameMatrix, Matrix.det_one]

def jacobian {R : Type*} [CommRing R] (φ : CoeffRing →+* R) :
    Ideal (MvPolynomial (Fin 5) R) := Ideal.span (Set.range fun i =>
      pderiv i (MvPolynomial.map φ universalF))

theorem nonstandard_column_mem {R : Type*} [CommRing R] (φ : CoeffRing →+* R)
    {n : ℕ} {χ : ZMod 3} {e : Index n χ} (h : ¬ Standard e) :
    MvPolynomial.map φ (column e) ∈ jacobian φ := by
  classical
  simp only [column, dif_neg h, map_mul, ← pderiv_map]
  apply Ideal.mul_mem_left
  exact Ideal.subset_span ⟨pivot h, rfl⟩

end CycleQ2HiggsJacobianFrames
end

#print axioms CycleQ2HiggsJacobianFrames.seed_frameDet
