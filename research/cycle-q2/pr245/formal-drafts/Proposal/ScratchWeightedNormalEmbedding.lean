import Mathlib.Algebra.MvPolynomial.NoZeroDivisors
import Mathlib.Algebra.MvPolynomial.PDeriv
import Mathlib.RingTheory.LaurentSeries
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.Algebra.GroupWithZero.Action.Units
import Mathlib.Tactic

/-!
# Embedding the ambient function field at the generic hypersurface point

Polynomial normal translation has zero kernel. A polynomial in its kernel
vanishes on the hypersurface, hence is divisible by its equation. The first
transverse coefficient of the equation is nonzero, so the quotient again
belongs to the kernel. Total degree decreases at every division.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedNormalEmbedding

open MvPolynomial
variable {A K : Type*} [CommRing A] [IsDomain A] [Field K]
abbrev Pol (A : Type*) [CommRing A] := MvPolynomial (Fin 4) A

/-- A coordinate-preserving polynomial specialization with nonzero normal
linear coefficient embeds the whole ambient polynomial ring. -/
theorem translate_injective (v : Pol A →+* K) (q : Pol A →+* Polynomial K)
    (f : Pol A) (hk : ∀ p, v p = 0 → f ∣ p)
    (h₀ : ∀ p, (q p).coeff 0 = v p)
    (h₁ : (q f).coeff 1 = v (pderiv 0 f)) (hg : v (pderiv 0 f) ≠ 0) :
    Function.Injective q := by
  have hnf : q f ≠ 0 := fun h => hg (by simpa only [h, Polynomial.coeff_zero] using h₁.symm)
  have hf : f ≠ 0 := fun h => hnf (by simpa only [h, map_zero])
  have hdeg : 0 < f.totalDegree := by
    apply Nat.pos_of_ne_zero
    intro h
    have he := MvPolynomial.totalDegree_eq_zero_iff_eq_C.mp h
    exact hg (by conv_lhs => rw [he]; simp)
  refine (injective_iff_map_eq_zero q).mpr ?_
  suffices aux : ∀ n : ℕ, ∀ p : Pol A, p.totalDegree = n → q p = 0 → p = 0 by
    exact fun p hp => aux _ p rfl hp
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro p hpn hp
    obtain ⟨u, hu⟩ := hk p (by simpa only [hp, Polynomial.coeff_zero] using (h₀ p).symm)
    by_cases uz : u = 0
    · simp [hu, uz]
    have hn : u.totalDegree < n := by
      rw [hu, MvPolynomial.totalDegree_mul_of_isDomain hf uz] at hpn
      omega
    have hz : q u = 0 := by
      rw [hu, map_mul] at hp
      exact (mul_eq_zero.mp hp).resolve_left hnf
    exact (uz (ih _ hn u rfl hz)).elim

/-- Map the ambient field to the Laurent field using the polynomial normal
translation. The source and target are the actual fraction and series fields. -/
def ambientMap (q : Pol A →+* Polynomial K) (hq : Function.Injective q) :
    FractionRing (Pol A) →+* LaurentSeries K :=
  IsFractionRing.lift (g := (algebraMap (Polynomial K) (LaurentSeries K)).comp q)
    ((Polynomial.algebraMap_hahnSeries_injective (Γ := ℤ) (R := K)).comp hq)

theorem ambientMap_apply (q : Pol A →+* Polynomial K) (hq : Function.Injective q) (p : Pol A) :
    ambientMap q hq (algebraMap (Pol A) (FractionRing (Pol A)) p) =
      algebraMap (Polynomial K) (LaurentSeries K) (q p) :=
  IsFractionRing.lift_algebraMap _ _

theorem ambientMap_injective (q : Pol A →+* Polynomial K) (hq : Function.Injective q) :
    Function.Injective (ambientMap q hq) := (ambientMap q hq).injective

/-- The three-pole ambient rational function is sent to the actual quotient
of the translated polynomials. -/
theorem ambientMap_pole (q : Pol A →+* Polynomial K) (hq : Function.Injective q) (a f : Pol A) :
    ambientMap q hq (algebraMap (Pol A) (FractionRing (Pol A)) a /
      (algebraMap (Pol A) (FractionRing (Pol A)) f)^3) =
    algebraMap (Polynomial K) (LaurentSeries K) (q a) /
      (algebraMap (Polynomial K) (LaurentSeries K) (q f))^3 := by
  rw [map_div₀, map_pow, ambientMap_apply, ambientMap_apply]

end CycleQ2WeightedNormalEmbedding
end
#print axioms CycleQ2WeightedNormalEmbedding.translate_injective
#print axioms CycleQ2WeightedNormalEmbedding.ambientMap_apply

noncomputable section

namespace CycleQ2WeightedNormalWedge
open MvPolynomial KaehlerDifferential
open scoped KaehlerDifferential

variable {A S : Type*} [CommRing A] [CommRing S] [Algebra A S]

private theorem coordinate_chain_rule (v : MvPolynomial (Fin 4) A →ₐ[A] S)
    (q : MvPolynomial (Fin 4) A) :
    (D A S) (v q) = ∑ i, v (pderiv i q) • (D A S) (v (X i)) := by
  have hx (j : Fin 4) : (D A S) (v (X j)) =
      ∑ i, v (pderiv i (X j)) • (D A S) (v (X i)) := by
    classical
    simp [pderiv_X, Pi.single_apply, apply_ite]
  induction q using MvPolynomial.induction_on with
  | C c =>
    change (D A S) (v (algebraMap A _ c)) = _
    simp
  | add p q hp hq => simp only [map_add, add_smul, Finset.sum_add_distrib, hp, hq]
  | mul_X p j hp =>
    rw [map_mul, Derivation.leibniz, hp]
    conv_lhs => lhs; rw [hx j]
    simp only [Derivation.leibniz, smul_eq_mul, map_add, map_mul, add_smul,
      Finset.sum_add_distrib, Finset.smul_sum, mul_smul]

def coordinateForms (v : MvPolynomial (Fin 4) A →ₐ[A] S) (i : Fin 4) : Ω[S⁄A] :=
  D A S (v (X i))

/-- Differentiating the equation and wedging with the last three coordinate
differentials kills all terms except that of the invertible first partial. -/
theorem hypersurface_volume (v : MvPolynomial (Fin 4) A →ₐ[A] S)
    (f : MvPolynomial (Fin 4) A) (hf : v f = 0)
    (hg : IsUnit (v (pderiv 0 f))) :
    exteriorPower.ιMulti S 4 (coordinateForms v) = 0 := by
  let W := exteriorPower.ιMulti S 4 (M := Ω[S⁄A])
  let dx := coordinateForms v
  let L := W.toMultilinearMap.toLinearMap dx 0
  have h : (∑ i : Fin 4, v (pderiv i f) • dx i) = 0 := by
    simp only [dx, coordinateForms, ← coordinate_chain_rule, hf, map_zero]
  have hs := congrArg L h
  simp only [map_sum, map_smul, map_zero] at hs
  have hdup (j : Fin 4) (hj : j ≠ 0) : L (dx j) = 0 :=
    W.map_update_self dx hj.symm
  have hhead : L (dx 0) = W dx := by
    change W (Function.update dx 0 (dx 0)) = W dx
    rw [Function.update_eq_self]
  apply hg.smul_eq_zero.mp
  calc
    _ = v (pderiv 0 f) • L (dx 0) := by rw [hhead]
    _ = ∑ i : Fin 4, v (pderiv i f) • L (dx i) := by
      symm
      apply Finset.sum_eq_single (0 : Fin 4)
      · intro j _ hj
        rw [hdup j hj, smul_zero]
      · exact fun h => (h (Finset.mem_univ _)).elim
    _ = 0 := hs

/-- The translated coordinate volume has the exact transverse sign and
factor for the exterior power of the actual Kähler module. -/
theorem translated_volume (v : MvPolynomial (Fin 4) A →ₐ[A] S)
    (f : MvPolynomial (Fin 4) A) (hf : v f = 0) (hg : IsUnit (v (pderiv 0 f))) (t : S) :
    exteriorPower.ιMulti S 4 (Function.update (coordinateForms v) 0 (D A S (v (X 0) + t))) =
      exteriorPower.ιMulti S 4 (Function.update (coordinateForms v) 0 (D A S t)) := by
  rw [map_add, AlternatingMap.map_update_add]
  change exteriorPower.ιMulti S 4 (Function.update (coordinateForms v) 0 (coordinateForms v 0)) + _ = _
  rw [Function.update_eq_self, hypersurface_volume v f hf hg, zero_add]

/-- In the polynomial normal chart the transverse parameter is exactly X,
and all the original point coordinates map to constant polynomials. -/
theorem polynomial_translated_volume {K : Type*} [Field K] [Algebra A K]
    (v : MvPolynomial (Fin 4) A →ₐ[A] K) (f : MvPolynomial (Fin 4) A)
    (hf : v f = 0) (hg : v (pderiv 0 f) ≠ 0) :
    let e : MvPolynomial (Fin 4) A →ₐ[A] Polynomial K :=
      (IsScalarTower.toAlgHom A K (Polynomial K)).comp v
    exteriorPower.ιMulti (Polynomial K) 4
        (Function.update (coordinateForms e) 0 (D A _ (e (X 0) + Polynomial.X))) =
      exteriorPower.ιMulti (Polynomial K) 4
        (Function.update (coordinateForms e) 0 (D A _ Polynomial.X)) := by
  let e := (IsScalarTower.toAlgHom A K (Polynomial K)).comp v
  refine translated_volume e f ?_ ?_ Polynomial.X
  · change algebraMap K (Polynomial K) (v f) = 0
    rw [hf, map_zero]
  · exact (isUnit_iff_ne_zero.mpr hg).map (algebraMap K (Polynomial K))

end CycleQ2WeightedNormalWedge
end

#print axioms CycleQ2WeightedNormalWedge.polynomial_translated_volume
