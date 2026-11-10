import Mathlib.RingTheory.Trace.Basic
import Mathlib.RingTheory.Derivation.Basic
import Mathlib.Tactic

noncomputable section
open scoped BigOperators
namespace FiniteAlgebraTrace
variable {K A ι : Type*} [Field K] [CommRing A] [Algebra K A]
  [Fintype ι] [DecidableEq ι]

variable (b : Module.Basis ι K A) (D : Derivation ℤ K K) (E : Derivation ℤ A A)
variable (compatible : ∀ k, E (algebraMap K A k) = algebraMap K A (D k))
include b compatible

omit b [Fintype ι] [DecidableEq ι] in
lemma deriv_smul (k : K) (x : A) :
    E (k • x) = D k • x + k • E x := by
  simp [Algebra.smul_def, Derivation.leibniz, compatible, mul_comm]

lemma coeff_derivative (x : A) (i : ι) :
    b.repr (E x) i = D (b.repr x i) + ∑ j, b.repr x j * b.repr (E (b j)) i := by
  have hsum : E x = ∑ j, (D (b.repr x j) • b j + b.repr x j • E (b j)) := by
    calc
      E x = E (∑ j, b.repr x j • b j) := congrArg E (b.sum_repr x).symm
      _ = ∑ j, E (b.repr x j • b j) := map_sum E _ _
      _ = _ := by
        apply Finset.sum_congr rfl
        intro j _
        exact deriv_smul D E compatible _ _
  have h := congrArg (b.coord i) hsum
  rw [map_sum] at h
  simpa only [map_add, map_smul, Module.Basis.coord_apply,
    Module.Basis.repr_self, Finsupp.single_apply, smul_eq_mul,
    Finset.sum_add_distrib, mul_ite, mul_one, mul_zero,
    Finset.sum_ite_eq', Finset.mem_univ, if_true] using h

lemma multiplication_derivative (x : A) (i j : ι) :
    D (Algebra.leftMulMatrix b x i j) =
      Algebra.leftMulMatrix b (E x) i j +
        ∑ k, Algebra.leftMulMatrix b x i k * b.repr (E (b j)) k -
        ∑ k, Algebra.leftMulMatrix b x k j * b.repr (E (b k)) i := by
  have h := coeff_derivative b D E compatible (x*b j) i
  have hmul := congrFun (Algebra.leftMulMatrix_mulVec_repr b x (E (b j))) i
  simp only [Derivation.leibniz, smul_eq_mul, map_add, Finsupp.add_apply] at h
  simp only [Matrix.mulVec, dotProduct, Algebra.leftMulMatrix_eq_repr_mul] at hmul ⊢
  change (∑ k, b.repr (x*b k) i*b.repr (E (b j)) k) = b.repr (x*E (b j)) i at hmul
  rw [← hmul, mul_comm (b j) (E x)] at h
  linear_combination -h

/-- Compatible derivations commute with the ordinary trace of any finite free
commutative algebra. A field or etaleness assumption on the algebra is unnecessary. -/
theorem trace_derivation (x : A) :
    Algebra.trace K A (E x) = D (Algebra.trace K A x) := by
  rw [Algebra.trace_eq_matrix_trace b, Algebra.trace_eq_matrix_trace b]
  simp only [Matrix.trace, Matrix.diag_apply, map_sum, multiplication_derivative b D E compatible,
    Finset.sum_sub_distrib, Finset.sum_add_distrib]
  have hs : (∑ i, ∑ k, Algebra.leftMulMatrix b x i k*b.repr (E (b i)) k) =
      ∑ i, ∑ k, Algebra.leftMulMatrix b x k i*b.repr (E (b k)) i := by
    exact Finset.sum_comm
  rw [hs]
  ring


omit b compatible in
/-- Normalized trace for a commutative algebra with an explicit finite basis. -/
def averageTrace (_b : Module.Basis ι K A) : A →ₗ[K] K :=
  (Fintype.card ι : K)⁻¹ • Algebra.trace K A

omit compatible in
theorem averageTrace_matrix (x : A) :
    averageTrace b x = (Fintype.card ι : K)⁻¹ *
      Matrix.trace (Algebra.leftMulMatrix b x) := by
  simp only [averageTrace, LinearMap.smul_apply, smul_eq_mul,
    Algebra.trace_eq_matrix_trace b]

theorem averageTrace_derivation (x : A) :
    averageTrace b (E x) = D (averageTrace b x) := by
  simp only [averageTrace, LinearMap.smul_apply, smul_eq_mul]
  rw [Derivation.leibniz]
  have hc : D ((Fintype.card ι : K)⁻¹) = 0 := by
    rw [Derivation.leibniz_inv, D.map_natCast, smul_zero]
  simp only [hc, smul_eq_mul, mul_zero, add_zero]
  rw [trace_derivation b D E compatible]

omit compatible [DecidableEq ι] in
theorem averageTrace_algebraMap (hcard : (Fintype.card ι : K) ≠ 0) (k : K) :
    averageTrace b (algebraMap K A k) = k := by
  simp only [averageTrace, LinearMap.smul_apply, smul_eq_mul,
    Algebra.trace_algebraMap_of_basis b, nsmul_eq_mul]
  field_simp [hcard]

omit compatible in
theorem averageTrace_divergence {κ : Type*} [Fintype κ]
    (Ds : κ → Derivation ℤ K K) (Es : κ → Derivation ℤ A A)
    (comp : ∀ i k, Es i (algebraMap K A k) = algebraMap K A (Ds i k))
    (w : κ → A) :
    (∑ i, Ds i (averageTrace b (w i))) = averageTrace b (∑ i, Es i (w i)) := by
  rw [map_sum]
  apply Finset.sum_congr rfl
  intro i _
  exact (averageTrace_derivation b (Ds i) (Es i) (comp i) (w i)).symm

omit compatible in
/-- An actual upstairs ordinary-divergence solution in any finite free algebra
produces a base-field solution by its complete normalized algebra trace. -/
theorem averageTrace_descends_source {κ : Type*} [Fintype κ]
    (Ds : κ → Derivation ℤ K K) (Es : κ → Derivation ℤ A A)
    (comp : ∀ i k, Es i (algebraMap K A k) = algebraMap K A (Ds i k))
    (hcard : (Fintype.card ι : K) ≠ 0) (w : κ → A) (r : K)
    (equation : (∑ i, Es i (w i)) = algebraMap K A r) :
    (∑ i, Ds i (averageTrace b (w i))) = r := by
  rw [averageTrace_divergence b Ds Es comp, equation,
    averageTrace_algebraMap b hcard]

#print axioms trace_derivation
#print axioms averageTrace_matrix
#print axioms averageTrace_derivation
#print axioms averageTrace_algebraMap
#print axioms averageTrace_divergence
#print axioms averageTrace_descends_source
end FiniteAlgebraTrace
