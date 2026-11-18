import Proposal.ScratchFormalNormalPartials
import Proposal.ScratchWeightedNormalTaylor
import Proposal.ScratchWeightedNormalEmbedding
import Mathlib.GroupTheory.QuotientGroup.Defs
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials

/-!
# Differentiation after translation to a meromorphic normal coordinate

Writing the first affine coordinate as its value at a hypersurface point
plus a formal variable gives four local coordinate partial derivatives.
The tangential partial acting on an ambient rational function corrects
for the motion of the value of that first coordinate. These formulas apply
to rational functions whose denominators have a zero at the point, provided
the translated denominator is a nonzero Laurent series.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 600000
noncomputable section
namespace CycleQ2FormalNormalChain

open MvPolynomial CycleQ2WeightedNormalTaylor CycleQ2FormalNormalPartials
variable {A K : Type*} [CommRing A] [Field K] [CharZero K]
local instance coefficientAlgebra : Algebra ℤ (LaurentSeries K) := HahnSeries.instAlgebra

/-- Expand in the first affine coordinate while retaining the other three
coordinates in the coefficient field. -/
def expand (v : Pol A →+* K) : Pol A →+* LaurentSeries K :=
  ((HahnSeries.ofPowerSeries ℤ K).comp Polynomial.coeToPowerSeries.ringHom).comp (translate v)

private theorem expand_C (v : Pol A →+* K) (a : A) :
    expand v (C a) = HahnSeries.single 0 (v (C a)) := by
  simp only [expand, translate, RingHom.comp_apply, eval₂Hom_C,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]

private theorem expand_zero (v : Pol A →+* K) :
    expand v (X 0) = HahnSeries.single 0 (v (X 0)) + HahnSeries.single 1 1 := by
  simp only [expand, translate, RingHom.comp_apply, eval₂Hom_X', if_pos rfl, map_add,
    Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C, Polynomial.coe_X,
    HahnSeries.ofPowerSeries_C, HahnSeries.ofPowerSeries_X, HahnSeries.C_apply]

private theorem expand_succ (v : Pol A →+* K) (k : Fin 3) :
    expand v (X k.succ) = HahnSeries.single 0 (v (X k.succ)) := by
  simp only [expand, translate, RingHom.comp_apply, eval₂Hom_X', Fin.succ_ne_zero,
    if_false, Polynomial.coeToPowerSeries.ringHom_apply, Polynomial.coe_C,
    HahnSeries.ofPowerSeries_C, HahnSeries.C_apply]

private theorem differentiate_expand (v : Pol A →+* K)
    (δ : Derivation ℤ (LaurentSeries K) (LaurentSeries K)) (i : Fin 4)
    (hC : ∀ a : A, δ (expand v (C a)) = 0)
    (hX : ∀ k : Fin 4, δ (expand v (X k)) = expand v (pderiv i (X k))) (q : Pol A) :
    δ (expand v q) = expand v (pderiv i q) := by
  induction q using MvPolynomial.induction_on with
  | C a => rw [hC, pderiv_C, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p k hp =>
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, hp, hX, pderiv_mul, map_add] <;> ring

theorem normal_expand (v : Pol A →+* K) (q : Pol A) :
    normal (expand v q) = expand v (pderiv 0 q) := by
  apply differentiate_expand
  · intro a
    rw [expand_C, normal_C]
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · rw [expand_zero, map_add, normal_C, normal_t, zero_add, pderiv_X_self, map_one]
    · rw [expand_succ, normal_C, pderiv_X_of_ne (Fin.succ_ne_zero k), map_zero]

theorem spatial_expand (v : Pol A →+* K) (D : Derivation ℤ K K) (j : Fin 3)
    (hC : ∀ a : A, D (v (C a)) = 0)
    (hX : ∀ k : Fin 3, D (v (X k.succ)) = if k = j then 1 else 0) (q : Pol A) :
    spatial D (v (X 0)) (expand v q) = expand v (pderiv j.succ q) := by
  apply differentiate_expand
  · intro a
    rw [expand_C, spatial_C, hC, map_zero]
  · intro k
    refine Fin.cases ?_ (fun k => ?_) k
    · rw [expand_zero, map_add, spatial_C, spatial_t, add_neg_cancel,
        pderiv_X_of_ne (Fin.succ_ne_zero j).symm, map_zero]
    · rw [expand_succ, spatial_C, hX]
      by_cases hk : k = j
      · subst k
        rw [if_pos rfl, HahnSeries.single_zero_one, pderiv_X_self, map_one]
      · rw [if_neg hk, map_zero, pderiv_X_of_ne ((Fin.succ_injective _).ne hk), map_zero]

private theorem expand_quotient_rule (v : Pol A →+* K)
    (δ : Derivation ℤ (LaurentSeries K) (LaurentSeries K)) (i : Fin 4)
    (law : ∀ q, δ (expand v q) = expand v (pderiv i q)) (p q : Pol A) :
    δ (expand v p / expand v q) =
      expand v ((pderiv i p) * q - p * (pderiv i q)) / expand v q ^ 2 := by
  rw [Derivation.leibniz_div, law, law, map_sub, map_mul, map_mul]
  simp only [smul_eq_mul, div_eq_mul_inv, inv_pow] <;> ring

theorem normal_expand_quotient (v : Pol A →+* K) (p q : Pol A) :
    normal (expand v p / expand v q) =
      expand v ((pderiv 0 p) * q - p * (pderiv 0 q)) / expand v q ^ 2 :=
  expand_quotient_rule v normal 0 (normal_expand v) p q

theorem spatial_expand_quotient (v : Pol A →+* K) (D : Derivation ℤ K K) (j : Fin 3)
    (hC : ∀ a : A, D (v (C a)) = 0)
    (hX : ∀ k : Fin 3, D (v (X k.succ)) = if k = j then 1 else 0) (p q : Pol A) :
    spatial D (v (X 0)) (expand v p / expand v q) =
      expand v ((pderiv j.succ p) * q - p * (pderiv j.succ q)) / expand v q ^ 2 :=
  expand_quotient_rule v _ j.succ (spatial_expand v D j hC hX) p q

section MeromorphicField

variable [IsDomain A] (v : Pol A →+* K) (f : Pol A)
    (hker : ∀ q, v q = 0 → f ∣ q) (hn : v (pderiv 0 f) ≠ 0)
include hker hn

/-- Specialize the ambient field embedding to the actual translated
coordinate at this generic hypersurface point. -/
abbrev meromorphic : FractionRing (Pol A) →+* LaurentSeries K :=
  CycleQ2WeightedNormalEmbedding.ambientMap (translate v)
    (CycleQ2WeightedNormalEmbedding.translate_injective v (translate v) f hker
      (translate_coeff_zero v) (translate_coeff_one v f) hn)

theorem meromorphic_polynomial (q : Pol A) :
    meromorphic v f hker hn (algebraMap (Pol A) (FractionRing (Pol A)) q) = expand v q :=
  CycleQ2WeightedNormalEmbedding.ambientMap_apply _ _ q

omit hker hn in
/-- Ambient coordinate partial extended by the field quotient rule. -/
def ambientPartial (i : Fin 4) :
    Derivation ℤ (FractionRing (Pol A)) (FractionRing (Pol A)) :=
  HoldoutConstruction.extendRingDerivation ((pderiv i).restrictScalars ℤ)

private theorem meromorphic_derivation
    (δ : Derivation ℤ (LaurentSeries K) (LaurentSeries K)) (i : Fin 4)
    (law : ∀ q, δ (expand v q) = expand v (pderiv i q)) (a : FractionRing (Pol A)) :
    δ (meromorphic v f hker hn a) = meromorphic v f hker hn (ambientPartial i a) := by
  obtain ⟨p, q, _, rfl⟩ := IsFractionRing.div_surjective (Pol A) a
  change δ (meromorphic v f hker hn (_ / _)) =
    meromorphic v f hker hn ((HoldoutConstruction.extendRingDerivation _) (_ / _))
  simp only [map_div₀, Derivation.leibniz_div, smul_eq_mul,
    HoldoutConstruction.extendRingDerivation_apply, Derivation.restrictScalars_apply,
    map_mul, map_sub, map_inv₀, map_pow, meromorphic_polynomial, law]

theorem normal_meromorphic (a : FractionRing (Pol A)) :
    normal (meromorphic v f hker hn a) = meromorphic v f hker hn (ambientPartial 0 a) :=
  meromorphic_derivation v f hker hn _ 0 (normal_expand v) a

theorem spatial_meromorphic (D : Derivation ℤ K K) (j : Fin 3)
    (hC : ∀ a : A, D (v (C a)) = 0)
    (hX : ∀ k : Fin 3, D (v (X k.succ)) = if k = j then 1 else 0) (a : FractionRing (Pol A)) :
    spatial D (v (X 0)) (meromorphic v f hker hn a) =
      meromorphic v f hker hn (ambientPartial j.succ a) :=
  meromorphic_derivation v f hker hn _ j.succ (spatial_expand v D j hC hX) a

/-- Each coefficient of an ambient rational primitive has a Laurent
expansion, including when it has a pole on the divisor. The three
residue coefficients give the induced tangential primitive. -/
theorem residue_of_meromorphic_divergence (D : Fin 3 → Derivation ℤ K K)
    (hC : ∀ j (c : A), D j (v (C c)) = 0)
    (hX : ∀ j k : Fin 3, D j (v (X k.succ)) = if k = j then 1 else 0)
    (a t : FractionRing (Pol A)) (b : Fin 3 → FractionRing (Pol A))
    (he : ambientPartial 0 t + ∑ j, ambientPartial j.succ (b j) = a) :
    ∑ j, D j ((meromorphic v f hker hn (b j)).coeff (-1)) =
      (meromorphic v f hker hn a).coeff (-1) := by
  refine residue_of_ambient_divergence D (v (X 0)) (meromorphic v f hker hn a)
    (meromorphic v f hker hn t) (fun j => meromorphic v f hker hn (b j)) ?_
  have h := congrArg (meromorphic v f hker hn) he
  rw [map_add, map_sum] at h
  simpa only [normal_meromorphic, fun j =>
    spatial_meromorphic v f hker hn (D j) j (hC j) (hX j) (b j)] using h

end MeromorphicField

/-- Exterior differentiation in the signed omitted-coordinate frame of
the ambient rational function field. -/
def rationalBoundary (A : Type*) [CommRing A] [IsDomain A] :
    (FractionRing (Pol A) × (Fin 3 → FractionRing (Pol A))) →+ FractionRing (Pol A) where
  toFun u := ambientPartial 0 u.1 + ∑ j, ambientPartial j.succ (u.2 j)
  map_zero' := by simp
  map_add' u w := by simp [Finset.sum_add_distrib, add_add_add_comm]

/-- Exterior differentiation in the three-coordinate frame of the
hypersurface function field. -/
def tangentialBoundary (D : Fin 3 → Derivation ℤ K K) : (Fin 3 → K) →+ K where
  toFun u := ∑ j, D j (u j)
  map_zero' := by simp
  map_add' u w := by simp [Finset.sum_add_distrib]

section RationalClasses
variable [IsDomain A] (v : Pol A →+* K) (f : Pol A)
    (hker : ∀ q, v q = 0 → f ∣ q) (hn : v (pderiv 0 f) ≠ 0)
    (D : Fin 3 → Derivation ℤ K K)
    (hC : ∀ j (c : A), D j (v (C c)) = 0)
    (hX : ∀ j k : Fin 3, D j (v (X k.succ)) = if k = j then 1 else 0)

/-- The rational residue on top forms modulo rational exact forms.
Changing a representative by an ambient rational divergence changes
its residue by the divergence of three rational coefficients in the
residue field. -/
def classResidue :
    FractionRing (Pol A) ⧸ (rationalBoundary A).range →+
      K ⧸ (tangentialBoundary D).range :=
  QuotientAddGroup.map _ _
    ((HahnSeries.coeff.addMonoidHom (-1)).comp (meromorphic v f hker hn).toAddMonoidHom) (by
      rintro _ ⟨u, rfl⟩
      exact ⟨fun j => (meromorphic v f hker hn (u.2 j)).coeff (-1),
        residue_of_meromorphic_divergence v f hker hn D hC hX
          (rationalBoundary A u) u.1 u.2 rfl⟩)

theorem classResidue_mk (a : FractionRing (Pol A)) :
    classResidue v f hker hn D hC hX (QuotientAddGroup.mk' _ a) =
      QuotientAddGroup.mk' _ ((meromorphic v f hker hn a).coeff (-1)) := rfl

private theorem simple_pole_residue (a u : Polynomial K) (hu : u.coeff 0 ≠ 0) :
    (algebraMap (Polynomial K) (LaurentSeries K) a /
      algebraMap (Polynomial K) (LaurentSeries K) (Polynomial.X * u)).coeff (-1) =
      a.coeff 0 / u.coeff 0 := by
  let e := HahnSeries.ofPowerSeries ℤ K
  let U : PowerSeries K := u
  let R : PowerSeries K := a
  have hu' : PowerSeries.constantCoeff U ≠ 0 := hu
  have hi : (e U)⁻¹ = e U⁻¹ := by
    apply inv_eq_of_mul_eq_one_left
    rw [← map_mul, PowerSeries.inv_mul_cancel _ hu', map_one]
  have he : algebraMap (Polynomial K) (LaurentSeries K) a /
      algebraMap (Polynomial K) (LaurentSeries K) (Polynomial.X * u) =
      HahnSeries.single (-1) 1 * e (R * U⁻¹) := by
    rw [map_mul, show algebraMap (Polynomial K) (LaurentSeries K) Polynomial.X =
      HahnSeries.single 1 1 from by rw [Polynomial.algebraMap_hahnSeries_apply,
        Polynomial.coe_X, HahnSeries.ofPowerSeries_X]]
    change e R / (HahnSeries.single 1 1 * e U) = _
    rw [div_eq_mul_inv, mul_inv_rev, HahnSeries.inv_single, inv_one, hi, map_mul] <;> ring
  rw [he, HahnSeries.coeff_single_mul, one_mul, sub_self]
  change (HahnSeries.ofPowerSeries ℤ K (R * U⁻¹)).coeff ((0 : ℕ) : ℤ) = _
  rw [HahnSeries.ofPowerSeries_apply_coeff, PowerSeries.coeff_zero_eq_constantCoeff_apply,
    map_mul, PowerSeries.constantCoeff_inv]
  change a.coeff 0 * (u.coeff 0)⁻¹ = a.coeff 0 / u.coeff 0
  exact (div_eq_mul_inv _ _).symm

/-- For a simple logarithmic form, the meromorphic coefficient is
the restriction of its regular factor: the rational top form
`df/f ∧ (p/q) dz₁∧dz₂∧dz₃` has residue `v(p)/v(q)`. -/
theorem classResidue_log (hf : v f = 0) (p q : Pol A) (hq : v q ≠ 0) :
    classResidue v f hker hn D hC hX (QuotientAddGroup.mk' _
      (algebraMap (Pol A) (FractionRing (Pol A)) ((pderiv 0 f) * p) /
        algebraMap (Pol A) (FractionRing (Pol A)) (f * q))) =
      QuotientAddGroup.mk' _ (v p / v q) := by
  rw [classResidue_mk, map_div₀, meromorphic_polynomial, meromorphic_polynomial]
  apply congrArg (QuotientAddGroup.mk' _)
  change (algebraMap (Polynomial K) (LaurentSeries K) (translate v ((pderiv 0 f) * p)) /
      algebraMap (Polynomial K) (LaurentSeries K) (translate v (f * q))).coeff (-1) = _
  have hden : translate v (f * q) = Polynomial.X * ((translate v f).divX * translate v q) := by
    calc
      _ = translate v f * translate v q := map_mul _ _ _
      _ = (Polynomial.X * (translate v f).divX) * translate v q :=
        congrArg (fun x => x * translate v q) (translate_equation v f hf)
      _ = _ := mul_assoc _ _ _
  have hu : ((translate v f).divX * translate v q).coeff 0 ≠ 0 := by
    rw [Polynomial.mul_coeff_zero, (normal_unit_jets v f).1, translate_coeff_zero]
    exact mul_ne_zero hn hq
  rw [hden, simple_pole_residue _ _ hu, translate_coeff_zero, map_mul,
    Polynomial.mul_coeff_zero, (normal_unit_jets v f).1, translate_coeff_zero]
  field_simp [hn, hq]

end RationalClasses

end CycleQ2FormalNormalChain
end

#print axioms CycleQ2FormalNormalChain.normal_expand_quotient
#print axioms CycleQ2FormalNormalChain.spatial_expand_quotient
#print axioms CycleQ2FormalNormalChain.spatial_meromorphic
#print axioms CycleQ2FormalNormalChain.residue_of_meromorphic_divergence
#print axioms CycleQ2FormalNormalChain.classResidue_mk
#print axioms CycleQ2FormalNormalChain.classResidue_log
