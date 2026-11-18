import Proposal.GeometricMonicWeightedAffineEquation
import Proposal.GeometricMonicWeightedDenominator
import Proposal.GeometricMonicWeightedPrimitiveIdentity
import Mathlib.RingTheory.AlgebraicIndependent.Defs

/-!
# The principal open of a rational primitive

Starting with three rational coefficients in the generic hypersurface, take one
common spatial denominator and record a base coefficient detecting it. A second
base coefficient detects the normal to the chart. The same polynomial numerators
and denominator specialize throughout their intersection. On every integral
characteristic-zero fiber there they again give a rational primitive.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2MonicWeightedPrimitiveSpecialization

open MvPolynomial CycleQ2MonicWeightedAffineEquation
open CycleQ2MonicWeightedPrimitiveIdentity
open CycleQ2MonicWeightedDenominator (fiber slot)
open scoped nonZeroDivisors
variable {A B : Type} [CommRing A] [CommRing B]

abbrev ChartRing (f : Pol A) := AdjoinRoot (separate f)
abbrev Fld (f : Pol A) := FractionRing (ChartRing f)

def projection (f : Pol A) : Pol A →+* ChartRing f :=
  (AdjoinRoot.mk _).comp separate.toRingEquiv.toRingHom

theorem projection_surjective (f : Pol A) : Function.Surjective (projection f) :=
  AdjoinRoot.mk_surjective.comp separate.surjective

theorem projection_kernel (f q : Pol A) : projection f q = 0 ↔ f ∣ q := by
  change AdjoinRoot.mk _ (separate q) = 0 ↔ _
  rw [AdjoinRoot.mk_eq_zero]
  constructor
  · rintro ⟨p,hp⟩
    exact ⟨separate.symm p, separate.injective (by simpa only [map_mul, AlgEquiv.apply_symm_apply] using hp)⟩
  · rintro ⟨p,rfl⟩
    exact ⟨separate p, map_mul _ _ _⟩

theorem separate_map (φ : A →+* B) (q : Pol A) :
    separate (MvPolynomial.map φ q) = fiber φ (separate q) := by
  have hC {R : Type} [CommRing R] (a : R) :
      separate (C a : Pol R) = Polynomial.C (C a) := separate.commutes a
  have hX (j : Fin 4) : separate (X j : Pol B) = fiber φ (separate (X j : Pol A)) := by
    refine Fin.lastCases ?_ (fun i => ?_) j
    · simp only [separate_last, fiber, Polynomial.map_X]
    · simp only [separate_castSucc, fiber, Polynomial.map_C, MvPolynomial.map_X]
  induction q using MvPolynomial.induction_on with
  | C c => simp only [MvPolynomial.map_C, hC, fiber, Polynomial.map_C]
  | add p q hp hq => simp only [map_add, hp, hq, fiber, Polynomial.map_add]
  | mul_X p j hp => simp only [map_mul, MvPolynomial.map_X, hp, hX, fiber, Polynomial.map_mul]

private theorem specialization_nonzero (φ : A →+* B) (f q : Pol A)
    (h : CycleQ2MonicWeightedDenominator.specialize φ (separate f) (projection f q) ≠ 0) :
    projection (MvPolynomial.map φ f) (MvPolynomial.map φ q) ≠ 0 := by
  intro he
  apply h
  change AdjoinRoot.mk _ (fiber φ (separate q)) = 0
  apply AdjoinRoot.mk_eq_zero.mpr
  simpa only [← separate_map] using
    (AdjoinRoot.mk_eq_zero.mp he : separate (MvPolynomial.map φ f) ∣ separate (MvPolynomial.map φ q))

def fieldValue (f : Pol A) [IsDomain (ChartRing f)] : Pol A →+* Fld f :=
  value (K := Fld f) (projection f)

def direction (f : Pol A) [IsDomain (ChartRing f)] [CharZero (Fld f)]
    (hn : fieldValue f (normal f) ≠ 0) (j : Fin 3) :=
  tangent (K := Fld f) (projection f) (projection_surjective f) f (projection_kernel f) hn j

/-- Extract a single principal open and polynomial representatives from the
actual input elements of the function field and their divergence identity. -/
theorem spread {f : Pol A} [IsDomain A] [IsDomain (ChartRing f)] [CharZero (Fld f)]
    (hm : (separate f).Monic) (h3 : (separate f).natDegree = 3)
    (hn : fieldValue f (normal f) ≠ 0) (v : Fin 3 → Fld f)
    (hv : (∑ j, direction f hn j (v j)) = density (fieldValue f) f) :
    ∃ (a : A) (d : Pol A) (p : Fin 3 → Pol A), a ≠ 0 ∧
      (∀ j, v j = fieldValue f (p j) / fieldValue f d) ∧ f ∣ cleared f d p ∧
      ∀ {B : Type} [CommRing B] (φ : A →+* B), φ a ≠ 0 →
        projection (MvPolynomial.map φ f) (MvPolynomial.map φ d) ≠ 0 ∧
        projection (MvPolynomial.map φ f) (normal (MvPolynomial.map φ f)) ≠ 0 := by
  classical
  obtain ⟨d,n,a,ha,hnumer,hspec⟩ := CycleQ2MonicWeightedDenominator.spread_fractions hm h3 v
  obtain ⟨q,hq⟩ := projection_surjective f d.val
  choose p hp using fun j => projection_surjective f (n j)
  have hd : fieldValue f q ≠ 0 := by
    change algebraMap (ChartRing f) (Fld f) (projection f q) ≠ 0
    rw [hq]
    exact (IsFractionRing.to_map_eq_zero_iff).not.mpr (nonZeroDivisors.coe_ne_zero d)
  have frac (j : Fin 3) : v j = fieldValue f (p j) / fieldValue f q := by
    apply (eq_div_iff hd).mpr
    change v j * algebraMap _ (Fld f) (projection f q) = algebraMap _ (Fld f) (projection f (p j))
    rw [hq,hp,mul_comm,← hnumer j]
  have hnormal : projection f (normal f) ≠ 0 := by
    intro he
    apply hn
    exact (congrArg (algebraMap (ChartRing f) (Fld f)) he).trans (map_zero _)
  obtain ⟨i,m,hb,hs⟩ := CycleQ2MonicWeightedDenominator.exists_detecting_coefficient hm h3
    (projection f (normal f)) hnormal
  refine ⟨a * (slot hm (projection f (normal f)) i).coeff m,q,p,mul_ne_zero ha hb,frac,?_,?_⟩
  · apply (primitive_iff_divides (K := Fld f) (projection f) (projection_surjective f) f (projection_kernel f) hn p q hd).mp
    simpa only [direction, frac] using hv
  · intro B _ φ hφ
    rw [map_mul] at hφ
    constructor
    · apply specialization_nonzero
      rw [hq]
      exact hspec φ (left_ne_zero_of_mul hφ)
    · rw [normal,MvPolynomial.pderiv_map]
      exact specialization_nonzero φ f (normal f) (hs φ (right_ne_zero_of_mul hφ))

/-- The spatial multiple remains nonzero at each generic point of the three
weight-one coordinates. This also controls evaluation on the ordinary double
cover of the weighted pencil. -/
theorem spread_with_spatial_multiple {f : Pol A} [IsDomain A] [IsDomain (ChartRing f)]
    [CharZero (Fld f)] (hm : (separate f).Monic) (h3 : (separate f).natDegree = 3)
    (hn : fieldValue f (normal f) ≠ 0) (v : Fin 3 → Fld f)
    (hv : (∑ j, direction f hn j (v j)) = density (fieldValue f) f) :
    ∃ (a : A) (d : Pol A) (p : Fin 3 → Pol A) (q : Coords A), a ≠ 0 ∧
      (∀ j, v j = fieldValue f (p j) / fieldValue f d) ∧ f ∣ cleared f d p ∧
      projection f d ∣ AdjoinRoot.of (separate f) q ∧
      ∀ {B : Type} [CommRing B] (φ : A →+* B), φ a ≠ 0 →
        MvPolynomial.map φ q ≠ 0 ∧
        projection (MvPolynomial.map φ f) (normal (MvPolynomial.map φ f)) ≠ 0 := by
  obtain ⟨a,d,p,ha,hv',hdiv,hspec⟩ := spread hm h3 hn v hv
  have hd : projection f d ≠ 0 := by
    simpa only [MvPolynomial.map_id] using (hspec (RingHom.id A) ha).1
  obtain ⟨q,m,hq,hD⟩ := CycleQ2MonicWeightedDenominator.exists_spatial_multiple hm _ hd
  refine ⟨a * q.coeff m,d,p,q,mul_ne_zero ha hq,hv',hdiv,hD,?_⟩
  intro B _ φ hφ
  rw [map_mul] at hφ
  refine ⟨?_,(hspec φ (left_ne_zero_of_mul hφ)).2⟩
  intro h
  apply right_ne_zero_of_mul hφ
  rw [← MvPolynomial.coeff_map, h, MvPolynomial.coeff_zero]

theorem separate_spatial (q : Coords A) :
    separate (MvPolynomial.rename Fin.castSucc q) = Polynomial.C q := by
  induction q using MvPolynomial.induction_on with
  | C c => rw [rename_C]; exact separate.commutes c
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, rename_X, hp]
    exact congrArg (fun z => Polynomial.C p * z) (separate_castSucc (R := A) j)

/-- Evaluate the cubic quotient at an actual weighted point. -/
def evaluate {L : Type} [CommRing L] {f : Pol A} (v : Pol A →+* L) (hf : v f = 0) :
    ChartRing f →+* L :=
  Ideal.Quotient.lift _ (v.comp separate.symm.toRingEquiv.toRingHom) (by
    intro p hp
    obtain ⟨q,rfl⟩ := Ideal.mem_span_singleton.mp hp
    change v (separate.symm (separate f * q)) = 0
    rw [map_mul, AlgEquiv.symm_apply_apply, map_mul, hf, zero_mul])

@[simp] theorem evaluate_projection {L : Type} [CommRing L] {f : Pol A} (v : Pol A →+* L)
    (hf : v f = 0) (p : Pol A) : evaluate v hf (projection f p) = v p := by
  change v (separate.symm (separate p)) = v p
  rw [AlgEquiv.symm_apply_apply]

/-- The spatial multiple protects the actual denominator in any weighted
point with algebraically independent spatial coordinates over its coefficients. -/
theorem evaluated_denominator_ne_zero {L : Type} [Field L] [Algebra B L]
    {f d : Pol A} {q : Coords A} (H : projection f d ∣ AdjoinRoot.of (separate f) q)
    (φ : A →+* B) (hq : MvPolynomial.map φ q ≠ 0)
    (v : Pol A →+* L) (hf : v f = 0) (x : Fin 3 → L)
    (hx : AlgebraicIndependent B x) (hc : ∀ a, v (C a) = algebraMap B L (φ a))
    (hX : ∀ j : Fin 3, v (X j.castSucc) = x j) : v d ≠ 0 := by
  have hval (r : Coords A) : v (rename Fin.castSucc r) = aeval x (MvPolynomial.map φ r) := by
    induction r using MvPolynomial.induction_on with
    | C c => simp only [rename_C, MvPolynomial.map_C, aeval_C, hc]
    | add p q hp hq => simp only [map_add, hp, hq]
    | mul_X p j hp => simp only [map_mul, rename_X, MvPolynomial.map_X, aeval_X, hp, hX]
  have he : AdjoinRoot.of (separate f) q = projection f (rename Fin.castSucc q) :=
    congrArg (AdjoinRoot.mk (separate f)) (separate_spatial q).symm
  obtain ⟨k,hk⟩ := H
  have hk' := congrArg (evaluate v hf) hk
  rw [he,map_mul,evaluate_projection,evaluate_projection,hval] at hk'
  intro h
  rw [h,zero_mul] at hk'
  exact hq (hx.eq_zero_of_aeval_eq_zero _ hk')

/-- Evaluate the same rational primitive on the chosen fiber, preserving the
normal density and its second-order derivatives. -/
theorem specialize_primitive {f d : Pol A} {p : Fin 3 → Pol A}
    (H : f ∣ cleared f d p) (φ : A →+* B)
    [IsDomain (ChartRing (MvPolynomial.map φ f))] [CharZero (Fld (MvPolynomial.map φ f))]
    (hn : fieldValue (MvPolynomial.map φ f) (normal (MvPolynomial.map φ f)) ≠ 0)
    (hd : projection (MvPolynomial.map φ f) (MvPolynomial.map φ d) ≠ 0) :
    (∑ j, direction (MvPolynomial.map φ f) hn j
      (fieldValue (MvPolynomial.map φ f) (MvPolynomial.map φ (p j)) /
       fieldValue (MvPolynomial.map φ f) (MvPolynomial.map φ d))) =
      density (fieldValue (MvPolynomial.map φ f)) (MvPolynomial.map φ f) := by
  apply (primitive_iff_divides (K := Fld (MvPolynomial.map φ f)) _ (projection_surjective _) _ (projection_kernel _) hn _ _
    (IsFractionRing.to_map_eq_zero_iff.not.mpr hd)).mpr
  simpa only [map_cleared] using map_dvd (MvPolynomial.map φ) H

end CycleQ2MonicWeightedPrimitiveSpecialization
end

#print axioms CycleQ2MonicWeightedPrimitiveSpecialization.spread
#print axioms CycleQ2MonicWeightedPrimitiveSpecialization.spread_with_spatial_multiple
#print axioms CycleQ2MonicWeightedPrimitiveSpecialization.evaluated_denominator_ne_zero
#print axioms CycleQ2MonicWeightedPrimitiveSpecialization.specialize_primitive
