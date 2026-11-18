import Proposal.GeometricPoleReductionLocal

/-!
# Multiplication on the left by a differential

The exterior multiplication used in normal pole reduction agrees with
multiplication in the underlying exterior algebra. Consequently its
two left factors anticommute in every degree, also over rings of
characteristic two.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2LogWedge
open CycleQ2PoleReductionLocal (prepend prepend_generator)
variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

theorem prepend_val (n : ℕ) (x : M) (z : ⋀[R]^n M) :
    (prepend n x z : ExteriorAlgebra R M) =
      ExteriorAlgebra.ι R x * (z : ExteriorAlgebra R M) := by
  have eqn : (⋀[R]^(n+1) M).subtype.comp (prepend n x) =
      (LinearMap.mulLeft R (ExteriorAlgebra.ι R x)).comp (⋀[R]^n M).subtype := by
    apply exteriorPower.linearMap_ext
    ext v : 1
    change (prepend n x (exteriorPower.ιMulti R n v) : ExteriorAlgebra R M) = _
    rw [prepend_generator]
    change ExteriorAlgebra.ιMulti R (n+1) (Fin.cons x v) =
      ExteriorAlgebra.ι R x * ExteriorAlgebra.ιMulti R n v
    simp only [ExteriorAlgebra.ιMulti_succ_apply, Matrix.vecTail, Fin.cons_zero, Fin.cons_comp_succ]
  exact DFunLike.congr_fun eqn z

theorem prepend_swap (n : ℕ) (x y : M) (z : ⋀[R]^n M) :
    prepend (n+1) x (prepend n y z) = -prepend (n+1) y (prepend n x z) := by
  apply Subtype.ext
  simp only [Submodule.coe_neg, prepend_val, ← mul_assoc]
  rw [(eq_neg_iff_add_eq_zero.mpr (ExteriorAlgebra.ι_add_mul_swap (R := R) x y)), neg_mul]

theorem prepend_twice (n : ℕ) (x : M) (z : ⋀[R]^n M) :
    prepend (n+1) x (prepend n x z) = 0 := by
  apply Subtype.ext
  simp only [prepend_val, ← mul_assoc, ExteriorAlgebra.ι_sq_zero, zero_mul, Submodule.coe_zero]

theorem prepend_add (n : ℕ) (x y : M) (z : ⋀[R]^n M) :
    prepend n (x+y) z = prepend n x z + prepend n y z := by
  apply Subtype.ext
  simp only [Submodule.coe_add, prepend_val, map_add, add_mul]

theorem prepend_smul (n : ℕ) (c : R) (x : M) (z : ⋀[R]^n M) :
    prepend n (c • x) z = c • prepend n x z := by
  apply Subtype.ext
  simp only [SetLike.val_smul, prepend_val, map_smul, smul_mul_assoc]

/-- Two successive left exterior multiplications kill a symmetric array, in
every characteristic. The diagonal terms vanish individually. -/
theorem sum_prepend_symmetric {I : Type*} [Fintype I] (n : ℕ) (x : I → M)
    (e : I → I → ⋀[R]^n M) (he : ∀ i j, e i j = e j i) :
    (∑ i, ∑ j, prepend (n+1) (x i) (prepend n (x j) (e i j))) = 0 := by
  classical
  let t (i j : I) := prepend (n+1) (x i) (prepend n (x j) (e i j))
  change (∑ i, ∑ j, t i j) = 0
  rw [← Fintype.sum_prod_type' t]
  apply Finset.sum_involution (fun p _ => Prod.swap p)
  · rintro ⟨i, j⟩ _
    change t i j + t j i = 0
    apply eq_neg_iff_add_eq_zero.mp
    change prepend (n+1) (x i) (prepend n (x j) (e i j)) = -prepend (n+1) (x j) (prepend n (x i) (e j i))
    rw [he i j]
    exact prepend_swap _ _ _ _
  · rintro ⟨i, j⟩ _ hn eqn
    have hji : j = i := congrArg Prod.fst eqn
    subst j
    exact hn (prepend_twice n (x i) (e i i))
  · intro p _
    exact Finset.mem_univ _
  · intro p _
    exact Prod.swap_swap p

end CycleQ2LogWedge
end

#print axioms CycleQ2LogWedge.prepend_val
#print axioms CycleQ2LogWedge.prepend_swap
#print axioms CycleQ2LogWedge.prepend_twice
#print axioms CycleQ2LogWedge.sum_prepend_symmetric
