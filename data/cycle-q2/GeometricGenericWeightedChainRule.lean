import Mathlib.FieldTheory.IntermediateField.Adjoin.Defs
import Proposal.GeometricGenericWeightedPencilEquation

/-!
# Differentiating the weighted pencil in its relative coordinates

The relative derivations kill the deformation parameter and the pencil
ratio. Differentiating the weighted hypersurface equation at its actual
point therefore determines the derivative of the implicit coordinate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GenericWeightedChainRule

open MvPolynomial CycleQ2Bridge CycleQ2AffineClearing CycleQ2GenericSpecialization
  CycleQ2GenericPencilLift CycleQ2GenericWeightedCoordinates CycleQ2GenericWeightedPencilEquation

section ChainRule

variable {R K : Type} [CommRing R] [Field K] [Algebra ℂ K]
  (D : Derivation ℂ K K) (f : R →+* K) (x : Fin 5 → K)

private def chain (p : MvPolynomial (Fin 5) R) : Prop :=
  D (eval₂Hom f x p) = ∑ i, eval₂Hom f x (pderiv i p) * D (x i)

private theorem chain_C (c : R) (hc : D (f c) = 0) : chain D f x (C c) := by
  simp [chain, hc]

private theorem chain_X (i : Fin 5) : chain D f x (X i) := by
  classical
  simp [chain, pderiv_X, Pi.single_apply, apply_ite]

private theorem chain_add {p q : MvPolynomial (Fin 5) R} (hp : chain D f x p) (hq : chain D f x q) :
    chain D f x (p + q) := by
  change D _ = _
  simp only [map_add, add_mul, Finset.sum_add_distrib]
  exact congrArg₂ (· + ·) hp hq

private theorem chain_mul {p q : MvPolynomial (Fin 5) R} (hp : chain D f x p) (hq : chain D f x q) :
    chain D f x (p * q) := by
  unfold chain at hp hq ⊢
  simp only [map_mul, Derivation.leibniz, smul_eq_mul, hp, hq, map_add,
    add_mul, Finset.sum_add_distrib, Finset.mul_sum]
  apply congrArg₂ (· + ·) <;> apply Finset.sum_congr rfl <;> intros <;> ring

private theorem chain_pow {p : MvPolynomial (Fin 5) R} (hp : chain D f x p) (n : ℕ) :
    chain D f x (p ^ n) := by
  induction n with
  | zero => simpa only [pow_zero, map_one] using chain_C D f x 1 (by rw [map_one, D.map_one_eq_zero])
  | succ n ih => rw [pow_succ]; exact chain_mul D f x ih hp

theorem eval_chain_rule (hf : ∀ c, D (f c) = 0) (p : MvPolynomial (Fin 5) R) :
    D (eval₂Hom f x p) = ∑ i, eval₂Hom f x (pderiv i p) * D (x i) := by
  change chain D f x p
  induction p using MvPolynomial.induction_on with
  | C c => exact chain_C D f x c (hf c)
  | add p q hp hq => exact chain_add D f x hp hq
  | mul_X p i hp => exact chain_mul D f x hp (chain_X D f x i)

private theorem chain_map (hf : ∀ c, D (f c) = 0) (p : MvPolynomial (Fin 5) R) :
    chain D (RingHom.id K) x (MvPolynomial.map f p) := by
  change D (eval x (MvPolynomial.map f p)) =
    ∑ i, eval x (pderiv i (MvPolynomial.map f p)) * D (x i)
  simp only [pderiv_map, eval_map]
  exact eval_chain_rule D f x hf p

end ChainRule

section Fraction
variable {R K : Type} [CommRing R] [Field K] [Algebra ℂ K]

/-- Evaluate the coordinate partial of a quotient by the usual quotient rule. -/
def quotientPartial (f : R →+* K) (x : Fin 5 → K) (p q : MvPolynomial (Fin 5) R) (i : Fin 5) : K :=
  (eval₂Hom f x (pderiv i p) * eval₂Hom f x q -
    eval₂Hom f x p * eval₂Hom f x (pderiv i q)) / (eval₂Hom f x q) ^ 2

theorem eval_fraction_chain_rule (D : Derivation ℂ K K) (f : R →+* K)
    (hf : ∀ c, D (f c) = 0) (x : Fin 5 → K) (p q : MvPolynomial (Fin 5) R) :
    D (eval₂Hom f x p / eval₂Hom f x q) = ∑ i, quotientPartial f x p q i * D (x i) := by
  unfold quotientPartial
  rw [Derivation.leibniz_div, eval_chain_rule D f x hf p, eval_chain_rule D f x hf q]
  simp only [smul_eq_mul, Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro i _
  simp only [div_eq_mul_inv, inv_pow]
  ring

end Fraction

theorem parameter_coefficients_constant {K : Type} [Field K] [Algebra ℂ K]
    (D : Derivation ℂ K K) (τ l : K) (hτ : D τ = 0) (hl : D l = 0)
    (c : MvPolynomial (Fin 2) ℂ) :
    D (eval₂Hom (algebraMap ℂ K) ![τ, l] c) = 0 := by
  have hx (i : Fin 2) : D (![τ, l] i) = 0 := by
    fin_cases i
    · exact hτ
    · exact hl
  induction c using MvPolynomial.induction_on with
  | C c => simp only [eval₂Hom_C, D.map_algebraMap]
  | add a b ha hb => simp only [map_add, ha, hb, add_zero]
  | mul_X a i ha => simp only [map_mul, eval₂Hom_X', Derivation.leibniz, ha, hx, smul_zero, add_zero]

/-- The entire coefficient field generated over the complex numbers is constant. -/
theorem adjoin_parameters_constant {K : Type} [Field K] [Algebra ℂ K]
    (D : Derivation ℂ K K) (τ l : K) (hτ : D τ = 0) (hl : D l = 0)
    (r : IntermediateField.adjoin ℂ ({τ, l} : Set K)) : D (r : K) = 0 := by
  refine IntermediateField.adjoin_induction ℂ (p := fun x _ => D x = 0) ?_
    D.map_algebraMap ?_ ?_ ?_ r.property
  · intro x hx
    rcases Set.mem_insert_iff.mp hx with h | h
    · exact h ▸ hτ
    · exact (Set.mem_singleton_iff.mp h) ▸ hl
  · intro x y _ _ hx hy
    rw [map_add, hx, hy, add_zero]
  · intro x _ hx
    rw [Derivation.leibniz_inv, hx, smul_zero]
  · intro x y _ _ hx hy
    rw [Derivation.leibniz, hx, hy, smul_zero, smul_zero, add_zero]

private theorem equation_chain (D : Derivation ℂ RF RF) (tau l : RF)
    (ht : D tau = 0) (hl : D l = 0) (h : WeightedPoly) :
    D (eval weightedPoint (equation tau l h)) =
      ∑ i, eval weightedPoint (pderiv i (equation tau l h)) * D (weightedPoint i) := by
  change chain D (RingHom.id RF) weightedPoint (equation tau l h)
  have h₆ : D (1 + l ^ 6) = 0 := by
    simp only [map_add, D.map_one_eq_zero, D.leibniz_pow, hl, smul_zero, add_zero]
  have h₂ : D (1 / 2) = 0 := by
    rw [one_div, D.leibniz_inv, show D 2 = 0 from D.map_natCast 2, smul_zero]
  let F := RingHom.id RF
  let H := chain D F weightedPoint
  have add {p q : MvPolynomial (Fin 5) RF} (hp : H p) (hq : H q) : H (p + q) :=
    chain_add D F weightedPoint hp hq
  have mul {p q : MvPolynomial (Fin 5) RF} (hp : H p) (hq : H q) : H (p * q) :=
    chain_mul D F weightedPoint hp hq
  have X' (i : Fin 5) : H (X i) := chain_X D F weightedPoint i
  have pow (i : Fin 5) (n : ℕ) : H (X i ^ n) := chain_pow D F weightedPoint (X' i) n
  have C' (a : RF) (ha : D a = 0) : H (C a) := chain_C D F weightedPoint a ha
  have hτ := C' _ ht
  have hl' := C' _ hl
  have h₆' := C' _ h₆
  have h₂' := C' _ h₂
  have hh := chain_map D (algebraMap ℂ RF) weightedPoint D.map_algebraMap h
  change H (equation tau l h)
  unfold equation
  with_reducible
    repeat' first | assumption | apply add | apply mul | apply pow | apply X'

theorem weighted_coordinate_sum (d : Direction) (j : Fin 3) (F : Fin 5 → RF) :
    ∑ i, F i * relativeDerivation d j (weightedPoint i) =
      F 1 * relativeDerivation d j (z 0) + F j.succ.succ := by
  have hcoord (k : Fin 3) : weightedPoint k.succ.succ = relativeCoordinate k := by
    fin_cases k <;> rfl
  have hsum : ∑ k : Fin 3, F k.succ.succ * relativeDerivation d j (weightedPoint k.succ.succ) =
      F j.succ.succ := by
    simp [hcoord, relativeDerivation_coordinate]
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ, hsum]
  change F 0 * relativeDerivation d j 1 + _ = _
  rw [Derivation.map_one_eq_zero, mul_zero, zero_add]
  rfl

open CycleQ2IncidenceNormalForm

variable (c : FullInvariantIndex 6 → ℂ) (hc : endpointDifference c ≠ 0)

abbrev endpointEquation := equation (parameter (endpointDirection c hc)) lambda (endpointDifference c)

theorem normal_coordinate (j : Fin 3) :
    relativeDerivation (endpointDirection c hc) j (z 0) =
      -eval weightedPoint (pderiv j.succ.succ (endpointEquation c hc)) /
        eval weightedPoint (pderiv 1 (endpointEquation c hc)) := by
  let d := endpointDirection c hc
  have h := equation_chain (relativeDerivation d j) (parameter d) lambda
    (relative_tau d j) (relative_lambda d j) (endpointDifference c)
  rw [endpoint_equation c hc, map_zero, weighted_coordinate_sum] at h
  apply (eq_div_iff (endpoint_normal_ne_zero c hc)).mpr
  rw [mul_comm]
  exact eq_neg_of_add_eq_zero_left h.symm

/-- The directional derivative after solving for the second weighted coordinate. -/
theorem weighted_derivative {R : Type} [CommRing R] (j : Fin 3) (f : R →+* RF)
    (hf : ∀ a, relativeDerivation (endpointDirection c hc) j (f a) = 0)
    (p : MvPolynomial (Fin 5) R) :
    relativeDerivation (endpointDirection c hc) j (eval₂Hom f weightedPoint p) =
      eval₂Hom f weightedPoint (pderiv j.succ.succ p) -
        eval₂Hom f weightedPoint (pderiv 1 p) *
        eval weightedPoint (pderiv j.succ.succ (endpointEquation c hc)) /
          eval weightedPoint (pderiv 1 (endpointEquation c hc)) := by
  rw [eval_chain_rule _ f weightedPoint hf p, weighted_coordinate_sum, normal_coordinate c hc]
  ring

theorem weighted_fraction_derivative {R : Type} [CommRing R] (j : Fin 3) (f : R →+* RF)
    (hf : ∀ a, relativeDerivation (endpointDirection c hc) j (f a) = 0)
    (p q : MvPolynomial (Fin 5) R) :
    relativeDerivation (endpointDirection c hc) j
        (eval₂Hom f weightedPoint p / eval₂Hom f weightedPoint q) =
      quotientPartial f weightedPoint p q j.succ.succ -
        quotientPartial f weightedPoint p q 1 *
          eval weightedPoint (pderiv j.succ.succ (endpointEquation c hc)) /
            eval weightedPoint (pderiv 1 (endpointEquation c hc)) := by
  rw [eval_fraction_chain_rule _ f hf weightedPoint p q, weighted_coordinate_sum, normal_coordinate c hc]
  ring

end CycleQ2GenericWeightedChainRule
end

#print axioms CycleQ2GenericWeightedChainRule.normal_coordinate
#print axioms CycleQ2GenericWeightedChainRule.weighted_derivative
#print axioms CycleQ2GenericWeightedChainRule.weighted_fraction_derivative
