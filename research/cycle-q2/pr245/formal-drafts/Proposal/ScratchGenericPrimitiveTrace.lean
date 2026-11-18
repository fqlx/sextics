import Proposal.GeometricTarget01Part01
import Mathlib.FieldTheory.Perfect

/-!
# Descent of a relative primitive across finite extensions of constants

A relative derivation kills every element separably algebraic over its
constant field. In a finite extension of the spatial function field this
identifies the three native tangent derivations on polynomials with those
on the extended chart. Normalized trace recovers the primitive on the
initial spatial function field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2WeightedGenericPrimitiveTrace

open CycleQ2FiniteDifferentialDescent MvPolynomial
open scoped BigOperators

variable {K L : Type*} [Field K] [Field L]

/-- Promote an absolute field derivation to a relative one using the
given field of constants. -/
def relative {k : Type*} [Field k] [Algebra k L]
    (δ : Derivation ℤ L L) (h : ∀ a : k, δ (algebraMap k L a) = 0) :
    Derivation k L L where
  toFun := δ
  map_add' := map_add δ
  map_smul' a x := by
    simp only [Algebra.smul_def, Derivation.leibniz, h, Algebra.algebraMap_self_apply, mul_zero, add_zero,
      RingHom.id_apply]
  map_one_eq_zero' := δ.map_one_eq_zero
  leibniz' := δ.leibniz

/-- Algebraic constants of the moving coefficient field remain
constants for the spatial derivation. -/
theorem kills_algebraic {k : Type*} [Field k] [CharZero k] [Algebra k L]
    (δ : Derivation ℤ L L) (h : ∀ a : k, δ (algebraMap k L a) = 0)
    {x : L} (hx : IsIntegral k x) : δ x = 0 := by
  have hn := (minpoly.irreducible hx).separable.aeval_derivative_ne_zero (minpoly.aeval k x)
  have he := congrArg (relative δ h) (minpoly.aeval k x)
  rw [Derivation.map_aeval, map_zero, smul_eq_mul] at he
  exact (mul_eq_zero.mp he).resolve_left hn

/-- Passing from a coefficient domain to its rational function field keeps
every coefficient constant. -/
theorem kills_fractions {A k : Type*} [CommRing A] [IsDomain A] [Field k]
    [Algebra A k] [IsFractionRing A k] (i : k →+* L) (δ : Derivation ℤ L L)
    (h : ∀ a, δ (i (algebraMap A k a)) = 0) (x : k) : δ (i x) = 0 := by
  obtain ⟨a, b, _, rfl⟩ := IsFractionRing.div_surjective A x
  rw [map_div₀, Derivation.leibniz_div, h a, h b]
  simp

variable [CharZero K] [Algebra K L] [FiniteDimensional K L]

theorem extend_kills_algebraic {k : Type*} [Field k] [CharZero k]
    [Algebra k K] [Algebra k L] [IsScalarTower k K L]
    (D : Derivation ℤ K K) (hk : ∀ c : k, D (algebraMap k K c) = 0)
    {x : L} (hx : IsIntegral k x) : extend D x = 0 := by
  refine kills_algebraic (extend D) (fun c => ?_) hx
  rw [IsScalarTower.algebraMap_apply k K L, extend_algebraMap, hk, map_zero]

/-- Any embedding of algebraic coefficients over the parameter field
is compatible with the canonical spatial derivatives. -/
theorem extend_kills_coefficient {k k' : Type*}
    [Field k] [CharZero k] [Field k'] [Algebra k k'] [Algebra.IsAlgebraic k k']
    [Algebra k K] [Algebra k L] [IsScalarTower k K L]
    (D : Derivation ℤ K K) (hk : ∀ c : k, D (algebraMap k K c) = 0)
    (i : k' →ₐ[k] L) (c : k') : extend D (i c) = 0 :=
  extend_kills_algebraic D hk (IsIntegral.map i (Algebra.IsAlgebraic.isAlgebraic c).isIntegral)

/-- The three relative spatial derivatives of a polynomial over an
algebraic coefficient extension are determined by their values on the
coordinate functions. In the eliminated coordinate this value is
the negative gradient ratio. -/
theorem tangent_rule {k' : Type*} [CommRing k']
    (v : MvPolynomial (Fin 4) k' →+* L) (δ : Derivation ℤ L L)
    (k : Fin 3) (ratio : L)
    (hc : ∀ c, δ (v (C c)) = 0)
    (hx : ∀ i, δ (v (X i)) =
      v (pderiv k.succ (X i)) - ratio * v (pderiv 0 (X i))) (q : MvPolynomial (Fin 4) k') :
    δ (v q) = v (pderiv k.succ q) - ratio * v (pderiv 0 q) := by
  induction q using MvPolynomial.induction_on with
  | C c => simp only [hc, pderiv_C, map_zero, mul_zero, sub_zero]
  | add p q hp hq => simp only [map_add, hp, hq]; ring
  | mul_X p i hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, hp, hx, map_add]
    ring

/-- Trace of a rational primitive is the original-field primitive;
there is no geometric connectedness or Galois requirement. -/
theorem divergence_descends {ι : Type*} [Fintype ι] (D : ι → Derivation ℤ K K)
    (r : K) (w : ι → L) (hw : ∑ i, extend (D i) (w i) = algebraMap K L r) :
    ∑ i, D i (Algebra.normalizedTrace K L (w i)) = r := by
  have ht := HoldoutConstruction.finiteNormalizedTrace_firstOrder D
    (fun i => extend (L := L) (D i)) (fun i x => extend_algebraMap (D i) x)
    (fun _ => 0) r w (by simpa only [map_zero, mul_zero, add_zero] using hw)
  simpa only [mul_zero, add_zero] using ht

end CycleQ2WeightedGenericPrimitiveTrace
end

#print axioms CycleQ2WeightedGenericPrimitiveTrace.extend_kills_coefficient
#print axioms CycleQ2WeightedGenericPrimitiveTrace.tangent_rule
#print axioms CycleQ2WeightedGenericPrimitiveTrace.divergence_descends
