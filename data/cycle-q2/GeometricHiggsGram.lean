import Proposal.GeometricHiggsSocle
import Mathlib.LinearAlgebra.Matrix.Nondegenerate

/-!
# Complementary monomials in the universal weighted Jacobian ring

The socle functional pairs each bounded Fermat monomial with its unique
complement. This gives a determinant with Fermat value one. Wherever this
determinant is nonzero and the functional descends to the Jacobian quotient,
both monomial families in the quotient are linearly independent.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2HiggsGram

open MvPolynomial Matrix CycleQ2FermatHiggs CycleQ2FermatJacobian
open CycleQ2GenericSexticGradient CycleQ2HiggsSocle

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Exponent of the unique complementary monomial in the Fermat socle box. -/
def complementExp (d : Exp) : Exp := exponent socle - d

omit [Fintype ι] [DecidableEq ι] in
theorem pair_exponents_eq_top_iff (e : ι → Exp) (hinj : Function.Injective e)
    (hbound : ∀ i, e i ≤ exponent socle) (i j : ι) :
    complementExp (e i) + e j = exponent socle ↔ i = j := by
  constructor
  · intro h
    apply hinj
    exact add_left_cancel ((tsub_add_cancel_of_le (hbound i)).trans h.symm)
  · rintro rfl
    exact tsub_add_cancel_of_le (hbound i)

/-- Entries and determinant are functions on the full coefficient space. -/
def gram (e : ι → Exp) : Matrix ι ι CoeffRing := Matrix.of fun i j =>
  CycleQ2HiggsSocle.trace
    (monomial (complementExp (e i)) 1 * monomial (e j) 1)

theorem gram_seed (e : ι → Exp) (hinj : Function.Injective e)
    (hbound : ∀ i, e i ≤ exponent socle) : (gram e).map seedEvaluation = 1 := by
  ext i j
  change seedEvaluation (CycleQ2HiggsSocle.trace _) = _
  rw [seed_trace]
  simp only [map_monomial, map_one, monomial_mul, one_mul, coeff_monomial,
    pair_exponents_eq_top_iff e hinj hbound, Matrix.one_apply]

theorem gram_det_seed (e : ι → Exp) (hinj : Function.Injective e)
    (hbound : ∀ i, e i ≤ exponent socle) : seedEvaluation (gram e).det = 1 := by
  rw [RingHom.map_det]
  change ((gram e).map seedEvaluation).det = 1
  rw [gram_seed e hinj hbound, Matrix.det_one]

omit [Fintype ι] [DecidableEq ι] in
theorem gram_map_entry {K : Type*} [CommRing K] (f : CoeffRing →+* K) (e : ι → Exp) (i j : ι) :
    (gram e).map f i j = traceAt f (monomial (complementExp (e i)) 1 * monomial (e j) 1) := by
  change f (CycleQ2HiggsSocle.trace _) = _
  rw [map_trace]
  simp only [map_mul, map_monomial, map_one]

/-- Every coefficient used by the universal functional has degree 18 and character 2. -/
theorem socle_row_weight (r : Row) :
    Finsupp.weight CycleQ2IncidenceNormalForm.fullGrading (CycleQ2HiggsSocle.exp r) = (18, 2) := by
  rw [CycleQ2IncidenceNormalForm.fullGrading_weight]
  apply Prod.ext
  · exact r.property.1
  · exact (ZMod.natCast_eq_natCast_iff' _ 2 3).mpr r.property.2

/-- Projecting an arbitrary polynomial onto the socle bidegree preserves its trace. -/
theorem traceAt_component {K : Type*} [CommRing K] (f : CoeffRing →+* K)
    (p : MvPolynomial (Fin 5) K) :
    traceAt f (weightedHomogeneousComponent CycleQ2IncidenceNormalForm.fullGrading (18, 2) p) =
      traceAt f p := by
  apply traceAt_congr
  funext r
  simp only [coefficients, LinearMap.pi_apply, lcoeff_apply, coeff_weightedHomogeneousComponent,
    if_pos (socle_row_weight r)]

private theorem independent_of_gram {K Q : Type*} [Field K] [CommRing Q] [Algebra K Q]
    (t : Q →ₗ[K] K) (x y : ι → Q) (M : Matrix ι ι K) (hdet : M.det ≠ 0)
    (hM : ∀ i j, M i j = t (y i * x j)) : LinearIndependent K x := by
  apply Fintype.linearIndependent_iff.mpr
  intro c hc i
  have hzero : M.mulVec c = 0 := by
    funext j
    let L := t.comp (LinearMap.mulLeft K (y j))
    have h := congrArg L hc
    simp only [map_sum, map_smul, map_zero, smul_eq_mul] at h
    change ∑ k, M j k * c k = 0
    simpa only [hM, LinearMap.comp_apply, LinearMap.mulLeft_apply, L, mul_comm] using h
  exact congrFun (Matrix.mulVec_injective_of_det_ne_zero hdet (hzero.trans (M.mulVec_zero).symm)) i

/-- The same nonvanishing determinant detects both families of actual quotient classes. -/
theorem independent_mod_ideal {K : Type*} [Field K] (f : CoeffRing →+* K) (e : ι → Exp)
    (I : Ideal (MvPolynomial (Fin 5) K)) (hI : ∀ p ∈ I, traceAt f p = 0)
    (hd : f (gram e).det ≠ 0) :
    LinearIndependent K (fun i => Ideal.Quotient.mk I (monomial (e i) 1)) ∧
      LinearIndependent K (fun i => Ideal.Quotient.mk I (monomial (complementExp (e i)) 1)) := by
  let t : (MvPolynomial (Fin 5) K ⧸ I) →ₗ[K] K :=
    (I.restrictScalars K).liftQ (traceAt f) (fun p hp => hI p hp)
  let x (i : ι) := Ideal.Quotient.mk I (monomial (e i) 1)
  let y (i : ι) := Ideal.Quotient.mk I (monomial (complementExp (e i)) 1)
  let M := (gram e).map f
  have hM : ∀ i j, M i j = t (y i * x j) := fun i j => gram_map_entry f e i j
  have hdet : M.det ≠ 0 := by rwa [RingHom.map_det] at hd
  refine ⟨independent_of_gram t x y M hdet hM, independent_of_gram t y x M.transpose ?_ ?_⟩
  · simpa only [Matrix.det_transpose] using hdet
  · intro i j
    rw [Matrix.transpose_apply, hM, mul_comm]

end CycleQ2HiggsGram
end

#print axioms CycleQ2HiggsGram.gram_det_seed
#print axioms CycleQ2HiggsGram.independent_mod_ideal
