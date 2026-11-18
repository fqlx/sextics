import Proposal.GeometricPoleReductionLocal

/-!
# Anticommutation of interior products

The contraction formula for a one-form wedged on the left gives
square-zero interior multiplication on exterior powers over any
commutative ring. Applying this result to the sum of two covectors
gives the signed identity for mixed contractions.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2LogInteriorAnti

open CycleQ2LiteralThreefoldResidueContraction (interior interior_wedge interior_add)
open CycleQ2PoleReductionLocal (prepend prepend_generator contract_prepend)

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

/-- Degree-zero instance of the contraction rule for left multiplication. -/
theorem interior_prepend_zero (L : M →ₗ[R] R) (a : M) (ω : ⋀[R]^0 M) :
    interior 0 L (prepend 0 a ω) = L a • ω := by
  have h : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 0)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction h using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [prepend_generator, interior_wedge, Fin.sum_univ_one]
    simp only [Fin.val_zero, pow_zero, one_smul, Fin.cons_zero]
    rw [show Fin.removeNth (α := fun _ => M) (0 : Fin 1) (Fin.cons a v) = v by funext j; exact j.elim0]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, smul_add]
  | smul c x _ hx => simp only [map_smul, hx, smul_comm c (L a)]

private theorem square_of_prepend (n : ℕ) (L : M →ₗ[R] R)
    (h : ∀ (a : M) (v : ⋀[R]^(n+1) M),
      interior n L (prepend n a (interior n L v)) = L a • interior n L v)
    (ω : ⋀[R]^(n+2) M) : interior n L (interior (n+1) L ω) = 0 := by
  have hω : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R (n+2))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hω using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [← Fin.cons_self_tail v, ← prepend_generator, contract_prepend, map_sub,
      map_smul, h, sub_self]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, hx, hy, add_zero]
  | smul c x _ hx => simp only [map_smul, hx, smul_zero]

/-- Applying the same interior contraction twice gives zero in every characteristic. -/
theorem interior_square (n : ℕ) (L : M →ₗ[R] R) (ω : ⋀[R]^(n+2) M) :
    interior n L (interior (n+1) L ω) = 0 := by
  induction n generalizing ω with
  | zero =>
    apply square_of_prepend
    intro a v
    exact interior_prepend_zero L a _
  | succ n ih =>
    apply square_of_prepend
    intro a v
    rw [contract_prepend, ih, map_zero, sub_zero]

/-- Two contractions anticommute on every exterior power. -/
theorem interior_swap (n : ℕ) (L Q : M →ₗ[R] R) (ω : ⋀[R]^(n+2) M) :
    interior n L (interior (n+1) Q ω) = -interior n Q (interior (n+1) L ω) := by
  have h := interior_square n (L + Q) ω
  simp only [interior_add, LinearMap.add_apply, map_add, interior_square,
    zero_add, add_zero] at h
  exact eq_neg_of_add_eq_zero_left h

end CycleQ2LogInteriorAnti
end

#print axioms CycleQ2LogInteriorAnti.interior_square
#print axioms CycleQ2LogInteriorAnti.interior_swap
