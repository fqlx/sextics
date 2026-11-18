import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.LinearAlgebra.Pi

/-!
# Linear realization of signed complementary-coordinate arrays

An alternating family of pair generators evaluates a skew array by summing
over its strictly upper-triangular coefficients. A skew elementary matrix
therefore represents its signed pair generator over every coefficient ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogIndexRealization

variable {K M I : Type} [CommRing K] [AddCommGroup M] [Module K M]
variable [Fintype I] [LinearOrder I]

/-- Extend a signed cofactor family linearly to coefficient vectors. -/
def vector (g : I → M) : (I → K) →ₗ[K] M where
  toFun v := ∑ i, v i • g i
  map_add' v w := by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c v := by simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum, smul_smul, smul_eq_mul]

theorem vector_single (g : I → M) (i : I) (a : K) :
    vector g (Pi.single i a) = a • g i := by
  change (∑ j, (Pi.single i a : I → K) j • g j) = _
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same]
  · intro j _ h
    rw [Pi.single_eq_of_ne h, zero_smul]
  · simp

/-- Count each oriented pair only once. -/
def matrix (g : I → I → M) : (I → I → K) →ₗ[K] M where
  toFun v := ∑ i, vector (fun j => if i < j then g i j else 0) (v i)
  map_add' v w := by simp only [Pi.add_apply, map_add, Finset.sum_add_distrib]
  map_smul' c v := by simp only [Pi.smul_apply, map_smul, RingHom.id_apply, Finset.smul_sum]

theorem matrix_single (g : I → I → M) (i j : I) (a : K) :
    matrix g (Pi.single i (Pi.single j a)) = a • (if i < j then g i j else 0) := by
  change (∑ l, vector (fun m => if l < m then g l m else 0) ((Pi.single i (Pi.single j a) : I → I → K) l)) = _
  rw [Finset.sum_eq_single i]
  · rw [Pi.single_eq_same, vector_single]
  · intro l _ h
    rw [Pi.single_eq_of_ne h, map_zero]
  · simp

theorem matrix_skew_single (g : I → I → M) (gsq : ∀ i, g i i = 0)
    (ganti : ∀ i j, g i j = -g j i) (i j : I) (a : K) :
    matrix g (Pi.single i (Pi.single j a) - Pi.single j (Pi.single i a)) = a • g i j := by
  rw [map_sub, matrix_single, matrix_single]
  rcases lt_trichotomy i j with h | rfl | h
  · simp [h, h.asymm]
  · simp [gsq]
  · simp only [if_neg h.asymm, if_pos h, smul_zero, zero_sub]
    rw [ganti i j, smul_neg]

end CycleQ2LogIndexRealization
end
#print axioms CycleQ2LogIndexRealization.matrix_skew_single
