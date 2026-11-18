import Proposal.GeometricLiteralThreefoldResidueContraction
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Normal contraction lowers the order of a closed meromorphic pole

On an open where a normal derivation sends the local equation to one,
contraction splits the leading exterior form into a term divisible by its
differential and a term divisible by the equation. The splitting computes
the regular numerator after the ordinary pole correction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2PoleReductionLocal

open CycleQ2LiteralThreefoldResidueContraction (interior interior_wedge)

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]

/-- Exterior multiplication by one vector, with that vector in the first slot. -/
def prepend (n : ℕ) (a : M) : (⋀[R]^n M) →ₗ[R] (⋀[R]^(n+1) M) :=
  exteriorPower.alternatingMapLinearEquiv ((exteriorPower.ιMulti R (n+1)).curryLeft a)

theorem prepend_generator (n : ℕ) (a : M) (v : Fin n → M) :
    prepend n a (exteriorPower.ιMulti R n v) = exteriorPower.ιMulti R (n+1) (Fin.cons a v) := by
  rw [prepend, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti] <;> rfl

private theorem omit_first (n : ℕ) (a : M) (v : Fin n → M) :
    Fin.removeNth (α := fun _ => M) (0 : Fin (n+1)) (Fin.cons a v) = v := by
  funext i
  simp [Fin.removeNth_apply]

private theorem omit_later (n : ℕ) (a : M) (v : Fin (n+1) → M) (i : Fin (n+1)) :
    Fin.removeNth (α := fun _ => M) i.succ (Fin.cons a v) = Fin.cons a (Fin.removeNth (α := fun _ => M) i v) :=
  Fin.cons_comp_succ_succAbove a v i

/-- Anticommutator of left exterior multiplication with contraction by a covector. -/
theorem contract_prepend (n : ℕ) (L : M →ₗ[R] R) (a : M) (ω : ⋀[R]^(n+1) M) :
    interior (n+1) L (prepend (n+1) a ω) =
      L a • ω - prepend n a (interior n L ω) := by
  have hm : ω ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R (n+1))) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hm using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, rfl⟩ := hx
    rw [prepend_generator, interior_wedge, Fin.sum_univ_succ, interior_wedge, map_sum]
    simp only [Fin.cons_zero, Fin.val_zero, pow_zero, one_smul, omit_first,
      Fin.cons_succ, Fin.val_succ, pow_succ, mul_neg_one, neg_smul, Finset.sum_neg_distrib,
      omit_later, map_zsmul, map_smul, prepend_generator, sub_eq_add_neg]
  | zero => simp
  | add x y _ _ hx hy => simp only [map_add, smul_add, hx, hy]; abel
  | smul c x _ hx => simp only [map_smul, hx, smul_sub, smul_comm c (L a)]

/-- If the leading normal wedge is divisible by f, the tangential remainder
after subtracting the canonical normal lift is also divisible by f. -/
theorem split_leading (n : ℕ) (L : M →ₗ[R] R) (a : M) (hL : L a = 1) (f : R)
    (ω : ⋀[R]^(n+1) M) (v : ⋀[R]^(n+2) M) (h : prepend (n+1) a ω = f • v) :
    ω = prepend n a (interior n L ω) + f • interior (n+1) L v := by
  have eqn := congrArg (interior (n+1) L) h
  rw [contract_prepend, hL, one_smul, map_smul] at eqn
  exact (sub_eq_iff_eq_add.mp eqn).trans (add_comm _ _)

/-- Bounded exterior derivative expressed after clearing one more power of
the pole implies divisibility of the leading normal wedge inside the regular
module. Here k is the unit given by the old pole order. -/
theorem normal_wedge_divisible (n : ℕ) (a : M) (f : R) (k : Rˣ)
    (ω : ⋀[R]^(n+1) M) (dω y : ⋀[R]^(n+2) M)
    (h : f • dω - (k : R) • prepend (n+1) a ω = f • y) :
    prepend (n+1) a ω = f • ((↑k⁻¹ : R) • (dω - y)) := by
  have eqn : (k : R) • prepend (n+1) a ω = f • dω - f • y := by
    rw [← h]
    abel
  have h' := congrArg ((↑k⁻¹ : R) • ·) eqn
  rw [smul_smul, k.inv_mul, one_smul] at h'
  calc
    _ = (↑k⁻¹ : R) • (f • dω - f • y) := h'
    _ = (↑k⁻¹ : R) • (f • (dω - y)) := congrArg ((↑k⁻¹ : R) • ·) (smul_sub f dω y).symm
    _ = _ := smul_comm _ _ _

/-- Cleared numerator of the correction by the differentiated pole
−ι_D ω/(k fᵏ). The argument dι is the regular numerator d(ι_D ω). -/
theorem lowered_numerator (n : ℕ) (L : M →ₗ[R] R) (a : M) (hL : L a = 1) (f k : R)
    (ω dι : ⋀[R]^(n+1) M) (v : ⋀[R]^(n+2) M) (h : prepend (n+1) a ω = f • v) :
    k • (ω - prepend n a (interior n L ω)) + f • dι =
      f • (k • interior (n+1) L v + dι) := by
  have hrem : ω - prepend n a (interior n L ω) = f • interior (n+1) L v := by
    exact sub_eq_iff_eq_add.mpr ((split_leading n L a hL f ω v h).trans (add_comm _ _))
  rw [hrem, smul_add, smul_comm k f]

/-- In a rank-five free module the sixth exterior power vanishes. -/
theorem six_subsingleton (b : Module.Basis (Fin 5) R M) : Subsingleton (⋀[R]^6 M) := by
  constructor
  intro x y
  apply (b.exteriorPower 6).repr.injective
  ext s
  have h := Finset.card_le_univ s.1
  simp at h

/-- Wedging an arbitrary covector evaluation against a single contraction
of the top form. -/
theorem top_wedge (b : Module.Basis (Fin 5) R M) (L : M →ₗ[R] R) (a : M)
    (W : ⋀[R]^5 M) :
    prepend 4 a (interior 4 L W) = L a • W := by
  haveI := six_subsingleton b
  have ht : prepend 5 a W = 0 := Subsingleton.elim _ _
  have h := contract_prepend 4 L a W
  rw [ht, map_zero] at h
  exact (sub_eq_zero.mp h.symm).symm

theorem top_double_wedge (b : Module.Basis (Fin 5) R M) (s t : M →ₗ[R] R) (a : M)
    (W : ⋀[R]^5 M) :
    prepend 3 a (interior 3 s (interior 4 t W)) =
      s a • interior 4 t W - t a • interior 4 s W := by
  have h := contract_prepend 3 s a (interior 4 t W)
  rw [top_wedge b t a W, map_smul] at h
  rw [h]
  abel

/-- A normalized normal contraction reconstructs any top form on the five-variable cone. -/
theorem top_normal (b : Module.Basis (Fin 5) R M) (L : M →ₗ[R] R) (a : M)
    (hL : L a = 1) (W : ⋀[R]^5 M) :
    prepend 4 a (interior 4 L W) = W := by
  rw [top_wedge b L a W, hL, one_smul]

/-- The normal wedge of the double contraction on an overlap is the
difference of the first contractions, with the order of the two normals explicit. -/
theorem top_double_normal (b : Module.Basis (Fin 5) R M) (s t : M →ₗ[R] R) (a : M)
    (hs : s a = 1) (ht : t a = 1) (W : ⋀[R]^5 M) :
    prepend 3 a (interior 3 s (interior 4 t W)) = interior 4 t W - interior 4 s W := by
  rw [top_double_wedge b s t a W, hs, ht, one_smul, one_smul]

/-- On three gradient opens the corresponding identity is the alternating
face sum of the double contractions. -/
theorem top_triple_normal (b : Module.Basis (Fin 5) R M) (s t u : M →ₗ[R] R) (a : M)
    (hs : s a = 1) (ht : t a = 1) (hu : u a = 1) (W : ⋀[R]^5 M) :
    prepend 2 a (interior 2 s (interior 3 t (interior 4 u W))) =
      interior 3 t (interior 4 u W) - interior 3 s (interior 4 u W) +
        interior 3 s (interior 4 t W) := by
  have h := contract_prepend 2 s a (interior 3 t (interior 4 u W))
  rw [top_double_normal b t u a ht hu W, map_sub, hs, one_smul] at h
  have e : prepend 2 a (interior 2 s (interior 3 t (interior 4 u W))) =
      interior 3 t (interior 4 u W) -
        (interior 3 s (interior 4 u W) - interior 3 s (interior 4 t W)) := by
    rw [h]
    abel
  rw [e]
  abel

section Differential
variable {A : Type} [CommRing A] [Algebra A R]

/-- Apply the normal splitting directly to the universal differential of f
in the true relative Kähler module. -/
theorem split_pole (n : ℕ) (D : Derivation A R R) (f : R) (hD : D f = 1)
    (ω : ⋀[R]^(n+1) (KaehlerDifferential A R))
    (v : ⋀[R]^(n+2) (KaehlerDifferential A R))
    (h : prepend (n+1) (KaehlerDifferential.D A R f) ω = f • v) :
    ω = prepend n (KaehlerDifferential.D A R f) (interior n D.liftKaehlerDifferential ω) +
      f • interior (n+1) D.liftKaehlerDifferential v := by
  exact split_leading n D.liftKaehlerDifferential (KaehlerDifferential.D A R f)
    ((D.liftKaehlerDifferential_comp_D f).trans hD) f ω v h

end Differential
end CycleQ2PoleReductionLocal
end

#print axioms CycleQ2PoleReductionLocal.contract_prepend
#print axioms CycleQ2PoleReductionLocal.lowered_numerator
#print axioms CycleQ2PoleReductionLocal.split_pole

#print axioms CycleQ2PoleReductionLocal.top_normal
#print axioms CycleQ2PoleReductionLocal.top_double_normal
#print axioms CycleQ2PoleReductionLocal.top_triple_normal
