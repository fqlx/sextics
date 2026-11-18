import Mathlib.AlgebraicGeometry.Morphisms.Smooth
import Mathlib.RingTheory.DedekindDomain.Dvr
import Mathlib.RingTheory.Finiteness.Quotient
import Mathlib.RingTheory.Flat.TorsionFree
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.LocalRing.ResidueField.Instances
import Mathlib.RingTheory.Smooth.Fiber
import Mathlib.RingTheory.Smooth.Field
import Mathlib.RingTheory.Unramified.LocalRing

/-!
# Smoothness of a finite-type Dedekind domain over a perfect field

A local uniformizer at a closed point gives an étale coordinate over the
affine line. Smoothness then follows at every generalization of the point.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

open IsLocalRing Polynomial
open scoped Polynomial

namespace CycleQ2NormalCurveSmooth

variable {K A : Type*} [Field K] [PerfectField K] [CommRing A]
  [Algebra K A] [Algebra.FiniteType K A]

/-- A uniformizer on the localization at a nonzero prime can be chosen in the original ring. -/
theorem exists_local_parameter [IsDedekindDomain A] (q : Ideal A) [q.IsPrime] (hq : q ≠ ⊥) :
    ∃ a ∈ q, a ≠ 0 ∧ maximalIdeal (Localization.AtPrime q) =
      Ideal.span {algebraMap A (Localization.AtPrime q) a} := by
  let B := Localization.AtPrime q
  have : IsDiscreteValuationRing B :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain A hq B
  obtain ⟨z, hz⟩ := IsDiscreteValuationRing.exists_irreducible B
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj q.primeCompl z
  change z * algebraMap A B s = algebraMap A B a at hs
  have ha : Associated z (algebraMap A B a) := by
    rw [← hs]
    exact associated_mul_unit_right _ _ (IsLocalization.map_units B s)
  have hgen := hz.maximalIdeal_eq.trans (Ideal.span_singleton_eq_span_singleton.mpr ha)
  refine ⟨a, (IsLocalization.AtPrime.to_map_mem_maximal_iff B q a).mp ?_, ?_, hgen⟩
  · rw [hgen]
    exact Ideal.subset_span (Set.mem_singleton _)
  · intro he
    exact (ha.irreducible hz).ne_zero (by simp [he])

/-- A uniformizer defines an étale coordinate, giving smoothness at the closed point. -/
theorem isSmoothAt_of_local_parameter [IsDomain A] (q : Ideal A) [q.IsMaximal] (a : A) (ha : a ∈ q)
    (h0 : a ≠ 0) (hgen : maximalIdeal (Localization.AtPrime q) =
      Ideal.span {algebraMap A (Localization.AtPrime q) a}) : Algebra.IsSmoothAt K q := by
  let : Algebra K[X] A := (aeval a).toAlgebra
  have : IsScalarTower K K[X] A := .of_algebraMap_eq fun x ↦ ((aeval a).commutes x).symm
  have : Algebra.FiniteType K[X] A := .of_restrictScalars_finiteType K _ _
  have : Algebra.FinitePresentation K[X] A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  have : Module.IsTorsionFree K[X] A := Module.isTorsionFree_iff_algebraMap_injective.mpr
    (transcendental_iff_injective.mp fun h ↦ (inferInstance : q.IsPrime).ne_top <|
      Ideal.eq_top_of_isUnit_mem _ ha ((isAlgebraic_iff_isIntegral.mp h).isUnit h0))
  let p := q.under K[X]
  have hX : (X : K[X]) ∈ p := by
    change aeval a (X : K[X]) ∈ q
    simpa using ha
  have : p.IsMaximal := Ideal.IsPrime.isMaximal inferInstance fun h ↦
    Polynomial.X_ne_zero (R := K) (by simpa [h] using hX)
  let := Localization.AtPrime.algebraOfLiesOver p q
  let := Ideal.Quotient.field p
  let := Ideal.Quotient.field q
  have : Module.Finite K (K[X] ⧸ p) := finite_of_finite_type_of_isJacobsonRing _ _
  have : PerfectField (K[X] ⧸ p) := Algebra.IsAlgebraic.perfectField K
  have : Module.Finite (K[X] ⧸ p) (A ⧸ q) :=
    finite_of_finite_type_of_isJacobsonRing _ _
  have : Algebra.IsUnramifiedAt K[X] q := by
    apply (Algebra.isUnramifiedAt_iff_map_eq _ p q).mpr
    refine ⟨inferInstance, le_antisymm ?_ ?_⟩
    · refine Ideal.map_le_iff_le_comap.mpr fun x hx ↦ ?_
      rw [Ideal.mem_comap, IsScalarTower.algebraMap_apply K[X] A (Localization.AtPrime q)]
      exact (IsLocalization.AtPrime.to_map_mem_maximal_iff _ q _).mpr hx
    · rw [hgen, Ideal.span_singleton_le_iff_mem]
      have he : algebraMap K[X] (Localization.AtPrime q) X =
          algebraMap A (Localization.AtPrime q) a := by
        rw [IsScalarTower.algebraMap_apply K[X] A (Localization.AtPrime q)]
        change algebraMap A (Localization.AtPrime q) (aeval a (X : K[X])) = _
        rw [aeval_X]
      rw [← he]
      exact Ideal.mem_map_of_mem _ hX
  have := Algebra.IsEtaleAt.of_isUnramifiedAt_of_flat (R := K[X]) q
  exact Algebra.FormallySmooth.comp K K[X] (Localization.AtPrime q)

/-- A finite-type normal affine curve over a perfect field is smooth. -/
theorem smooth_of_isDedekindDomain [IsDedekindDomain A] : Algebra.Smooth K A := by
  have : Algebra.FinitePresentation K A := Algebra.FinitePresentation.of_finiteType.mp ‹_›
  by_cases hF : IsField A
  · letI := hF.toField
    exact ⟨inferInstance, inferInstance⟩
  refine ⟨Algebra.smoothLocus_eq_univ_iff.mp (Set.eq_univ_iff_forall.mpr fun x ↦ ?_), ‹_›⟩
  obtain ⟨m, hm, hxm⟩ := x.asIdeal.exists_le_maximal x.isPrime.ne_top
  obtain ⟨a, ha, h0, hgen⟩ := exists_local_parameter m (Ring.ne_bot_of_isMaximal_of_not_isField hm hF)
  have hsm : (⟨m, hm.isPrime⟩ : PrimeSpectrum A) ∈ Algebra.smoothLocus K A :=
    isSmoothAt_of_local_parameter m a ha h0 hgen
  exact ((PrimeSpectrum.le_iff_specializes x ⟨m, hm.isPrime⟩).mp hxm).mem_open
    Algebra.isOpen_smoothLocus hsm

/-- Smoothness written in terms of normality, dimension and finite type on an affine chart. -/
theorem smooth_of_normal_affine_curve (K B : Type*) [Field K] [PerfectField K] [CommRing B]
    [IsDomain B] [Algebra K B] [Algebra.FiniteType K B]
    [Ring.KrullDimLE 1 B] [IsIntegrallyClosed B] : Algebra.Smooth K B := by
  have : Ring.DimensionLEOne B := ⟨fun hn hp ↦ hp.isMaximal_of_ne_bot hn⟩
  have : IsNoetherianRing B := Algebra.FiniteType.isNoetherianRing K B
  have : IsDedekindDomain B := { ‹IsDomain B›, ‹IsNoetherianRing B›,
    ‹Ring.DimensionLEOne B›, ‹IsIntegrallyClosed B› with }
  exact smooth_of_isDedekindDomain

/-- The finite integral closure of an affine curve domain in a field is smooth
over its perfect coefficient field. -/
theorem smooth_finite_integralClosure (K R L : Type*) [Field K] [PerfectField K]
    [CommRing R] [IsDomain R] [Algebra K R] [Algebra.FiniteType K R] [Ring.KrullDimLE 1 R]
    [Field L] [Algebra R L] [Module.Finite R (integralClosure R L)] :
    let := ((algebraMap R (integralClosure R L)).comp (algebraMap K R)).toAlgebra
    Algebra.Smooth K (integralClosure R L) := by
  have : Ring.DimensionLEOne R := ⟨fun hn hp ↦ hp.isMaximal_of_ne_bot hn⟩
  let B := integralClosure R L
  let := ((algebraMap R B).comp (algebraMap K R)).toAlgebra
  have : IsScalarTower K R B := .of_algebraMap_eq' rfl
  have : Algebra.FiniteType K B :=
    Algebra.FiniteType.trans (inferInstance : Algebra.FiniteType K R) inferInstance
  have : IsIntegrallyClosed B := IsIntegrallyClosed.of_isIntegrallyClosedIn B L
  exact smooth_of_normal_affine_curve K B

open AlgebraicGeometry CategoryTheory

universe u

/-- Normal affine curve charts cover a smooth scheme over a perfect field. -/
theorem smooth_of_normal_affine_cover (K : Type u) [Field K] [PerfectField K]
    {X : Scheme.{u}} (f : X ⟶ Spec (CommRingCat.of K)) (C : X.OpenCover)
    (B : C.I₀ → Type u) [∀ i, CommRing (B i)] [∀ i, IsDomain (B i)]
    [∀ i, Algebra K (B i)] [∀ i, Algebra.FiniteType K (B i)]
    [∀ i, Ring.KrullDimLE 1 (B i)] [∀ i, IsIntegrallyClosed (B i)]
    (e : ∀ i, C.X i ≅ Spec (CommRingCat.of (B i)))
    (he : ∀ i, C.f i ≫ f = (e i).hom ≫ Spec.map (CommRingCat.ofHom (algebraMap K (B i)))) :
    Smooth f := by
  refine (IsZariskiLocalAtSource.iff_of_openCover C).mpr fun i ↦ ?_
  rw [he]
  have : Smooth (Spec.map (CommRingCat.ofHom (algebraMap K (B i)))) :=
    (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
      (RingHom.smooth_algebraMap.mpr (smooth_of_normal_affine_curve K (B i)))
  infer_instance

end CycleQ2NormalCurveSmooth

#print axioms CycleQ2NormalCurveSmooth.smooth_of_normal_affine_curve

#print axioms CycleQ2NormalCurveSmooth.smooth_finite_integralClosure

#print axioms CycleQ2NormalCurveSmooth.smooth_of_normal_affine_cover
