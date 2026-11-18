import Proposal.GeometricSmoothImageDimension
import Proposal.GeometricLiteralTimeCurveReduced
import Mathlib.RingTheory.Unramified.LocalRing
import Mathlib.RingTheory.DiscreteValuationRing.TFAE
import Mathlib.RingTheory.Filtration
import Mathlib.RingTheory.LocalProperties.IntegrallyClosed

/-!
# Local normality of the smooth fixed-sextic parameter curve

An étale chart over the affine line identifies the maximal ideal of each
local ring as principal. Krull intersection then writes every nonzero
element as a power of its generator times a unit. Reducedness rules out
zero products of such elements. The resulting Noetherian local domains
are fields or discrete valuation rings, hence integrally closed.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeCurveLocalNormal

open CategoryTheory AlgebraicGeometry IsLocalRing CycleQ2LiteralIncidenceTimeCurve

private theorem factor {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R]
    {π : R} (hπ : maximalIdeal R = Ideal.span {π}) (a : R) (ha : a ≠ 0) :
    ∃ (n : ℕ) (u : R), IsUnit u ∧ a = π ^ n * u := by
  classical
  let m := maximalIdeal R
  have ex : ∃ n : ℕ, a ∉ m ^ (n + 1) := by
    by_contra! hn
    apply ha
    change a ∈ (⊥ : Ideal R)
    rw [← m.iInf_pow_eq_bot_of_isLocalRing (maximalIdeal.isMaximal R).ne_top,
      Submodule.mem_iInf]
    intro n
    cases n with
    | zero => simp
    | succ k => exact hn k
  let n := Nat.find ex
  have hn : a ∈ m ^ n := by
    cases e : n with
    | zero => simp
    | succ k =>
      by_contra h
      have hle := Nat.find_min' ex h
      change n ≤ k at hle
      omega
  have hnext : a ∉ m ^ (n + 1) := Nat.find_spec ex
  change a ∈ maximalIdeal R ^ n at hn
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton] at hn
  obtain ⟨u, hu⟩ := hn
  refine ⟨n, u, ?_, hu⟩
  by_contra hunit
  have hum : u ∈ maximalIdeal R := hunit
  rw [hπ, Ideal.mem_span_singleton] at hum
  obtain ⟨v, hv⟩ := hum
  apply hnext
  change a ∈ maximalIdeal R ^ (n+1)
  rw [hπ, Ideal.span_singleton_pow, Ideal.mem_span_singleton, pow_succ]
  exact ⟨v, by rw [hu, hv, mul_assoc]⟩

private theorem domain_of_principal_maximal {R : Type} [CommRing R] [IsLocalRing R]
    [IsNoetherianRing R] [_root_.IsReduced R] (h : (maximalIdeal R).IsPrincipal) :
    IsDomain R := by
  obtain ⟨π, hπ : maximalIdeal R = Ideal.span _⟩ := h
  by_cases hz : π = 0
  · exact (isField_iff_maximalIdeal_eq.mpr (by simpa [hz] using hπ)).isDomain
  apply (isDomain_iff_noZeroDivisors_and_nontrivial R).mpr
  refine ⟨⟨?_⟩, inferInstance⟩
  intro a b hab
  by_contra! h
  obtain ⟨n, u, hu, ha⟩ := factor hπ a h.1
  obtain ⟨m, v, hv, hb⟩ := factor hπ b h.2
  have hzpow : π ^ (n + m) * (u * v) = 0 := by
    rw [pow_add, mul_mul_mul_comm, ← ha, ← hb, hab]
  have hnil : IsNilpotent π := ⟨n + m, (hu.mul hv).isRegular.2.mul_right_eq_zero_iff.mp hzpow⟩
  exact hz (isNilpotent_iff_eq_zero.mp hnil)

private theorem stalk_principal (x : Curve) : (maximalIdeal (Curve.presheaf.stalk x)).IsPrincipal := by
  have := smooth_parameter_curve
  obtain ⟨R, j, hj, q, rfl, φ, _, hφ⟩ :=
    CycleQ2SweptSupport.exists_standard_affine_chart 1 toComplex x
  obtain ⟨g, _, hg⟩ := hφ.exists_etale_mvPolynomial
  let P := MvPolynomial (Fin 1) ℂ
  let : Algebra P R := g.toAlgebra
  have : Algebra.Etale P R := hg
  let p := q.asIdeal.under P
  let : Algebra (Localization.AtPrime p) (Localization.AtPrime q.asIdeal) :=
    Localization.AtPrime.algebraOfLiesOver p q.asIdeal
  let e := (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).symm.toRingEquiv
  have : IsPrincipalIdealRing P := IsPrincipalIdealRing.of_surjective e e.surjective
  have h := ((Algebra.isUnramifiedAt_iff_map_eq P p q.asIdeal).mp inferInstance).2
  have hq : (maximalIdeal (Localization.AtPrime q.asIdeal)).IsPrincipal := h ▸
    (IsPrincipalIdealRing.principal p).map_ringHom (algebraMap P (Localization.AtPrime q.asIdeal))
  let e' : Localization.AtPrime q.asIdeal ≃+* Curve.presheaf.stalk (j q) :=
    (StructureSheaf.stalkIso R q).toRingEquiv.trans (asIso (j.stalkMap q)).symm.commRingCatIsoToRingEquiv
  exact (IsLocalRing.map_ringEquiv_maximalIdeal e') ▸ hq.map_ringHom e'

private theorem curve_locallyNoetherian : IsLocallyNoetherian Curve := by
  have := smooth_parameter_curve
  have : Smooth toComplex := SmoothOfRelativeDimension.smooth 1 _
  exact LocallyOfFiniteType.isLocallyNoetherian toComplex

/-- Every actual local ring of the fixed-sextic time curve is a domain. -/
theorem stalk_isDomain (x : Curve) : IsDomain (Curve.presheaf.stalk x) := by
  have := curve_locallyNoetherian
  exact domain_of_principal_maximal (stalk_principal x)

attribute [local instance] stalk_isDomain

/-- Every actual local ring is a field or a discrete valuation ring. -/
theorem stalk_field_or_dvr (x : Curve) :
    IsField (Curve.presheaf.stalk x) ∨ IsDiscreteValuationRing (Curve.presheaf.stalk x) := by
  let R := Curve.presheaf.stalk x
  have := curve_locallyNoetherian
  have := stalk_isDomain x
  by_cases h : IsField R
  · exact Or.inl h
  · exact Or.inr (((IsDiscreteValuationRing.TFAE R h).out 4 0).mp (stalk_principal x))

/-- The local rings of the actual fixed-sextic curve are integrally closed. -/
theorem stalk_isIntegrallyClosed (x : Curve) : IsIntegrallyClosed (Curve.presheaf.stalk x) := by
  let R := Curve.presheaf.stalk x
  have := curve_locallyNoetherian
  have := stalk_isDomain x
  have : IsPrincipalIdealRing R :=
    ((tfae_of_isNoetherianRing_of_isLocalRing_of_isDomain R).out 4 0).mp (stalk_principal x)
  infer_instance

/-- The coordinate ring of an integral affine open in any open subscheme of the
fixed-sextic curve is integrally closed. -/
theorem affineOpen_isIntegrallyClosed_of_openImmersion {Y : Scheme.{0}} (j : Y ⟶ Curve)
    [IsOpenImmersion j] (W : Y.Opens) (hW : IsAffineOpen W) [IsDomain Γ(Y, W)] :
    IsIntegrallyClosed Γ(Y, W) := by
  apply IsIntegrallyClosed.of_localization_maximal
  intro p _ hp
  let q : Spec Γ(Y, W) := ⟨p, hp.isPrime⟩
  let k := hW.fromSpec ≫ j
  let e : Curve.presheaf.stalk (k q) ≃+* Localization.AtPrime p :=
    (asIso (k.stalkMap q)).commRingCatIsoToRingEquiv.trans
      (StructureSheaf.stalkIso Γ(Y, W) q).symm.toRingEquiv
  have := stalk_isIntegrallyClosed (k q)
  exact IsIntegrallyClosed.of_equiv e

#print axioms affineOpen_isIntegrallyClosed_of_openImmersion
#print axioms stalk_isDomain
#print axioms stalk_field_or_dvr
#print axioms stalk_isIntegrallyClosed

end CycleQ2LiteralTimeCurveLocalNormal
end
