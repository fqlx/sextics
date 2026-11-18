import Proposal.GeometricDenseOpenAffineSections
import Proposal.GeometricSmoothImageDimension
import Mathlib.AlgebraicGeometry.Noetherian
import Mathlib.RingTheory.DedekindDomain.Basic
import Mathlib.RingTheory.NoetherNormalization

/-!
# Affine chart dimension from a dense smooth curve

A Noether normalization of an affine chart maps its dense smooth open to
affine space. The residue-field transcendence-degree bound for that image
forces the normalization to have at most one polynomial variable.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2CurveChartDimension

open CategoryTheory AlgebraicGeometry TopologicalSpace CycleQ2SweptSupport

private def affinePresentation (K : Type) [Field K] (s : ℕ) :
    Algebra.PreSubmersivePresentation K (MvPolynomial (Fin s) K) (Fin s) Empty where
  toPresentation :=
    { toGenerators := Algebra.Generators.mvPolynomial K (Fin s)
      relation := Empty.elim
      span_range_relation_eq_ker := by rw [Algebra.Generators.ker_mvPolynomial]; simp }
  map := Empty.elim
  map_inj := by intro a; exact a.elim

private theorem affine_smooth (K : Type) [Field K] (s : ℕ) : SmoothOfRelativeDimension s
    (Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (Fin s) K))) := by
  let P : Algebra.SubmersivePresentation K (MvPolynomial (Fin s) K) (Fin s) Empty :=
    { toPreSubmersivePresentation := affinePresentation K s
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
          Matrix.det_isEmpty, map_one]
        exact isUnit_one }
  have hs : Algebra.IsStandardSmoothOfRelativeDimension s K (MvPolynomial (Fin s) K) :=
    P.isStandardSmoothOfRelativeDimension (by
      change Nat.card (Fin s) - Nat.card Empty = s
      simp [Nat.card_eq_fintype_card])
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension s)).mpr
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap s).mpr hs)

private theorem polynomial_dim (K : Type) [Field K] {s : ℕ} (hs : s ≤ 1) :
    Ring.DimensionLEOne (MvPolynomial (Fin s) K) := by
  interval_cases s
  · exact Ring.DimensionLEOne.of_ringEquiv (MvPolynomial.isEmptyRingEquiv K (Fin 0))
  · exact Ring.DimensionLEOne.of_ringEquiv (MvPolynomial.uniqueAlgEquiv K (Fin 1)).toRingEquiv

private theorem dim_of_finite {K : Type} [Field K] {s : ℕ} {A : Type} [CommRing A] [Algebra K A]
    (g : MvPolynomial (Fin s) K →ₐ[K] A) (hf : g.IsIntegral) (hs : s ≤ 1) :
    Ring.KrullDimLE 1 A := by
  let P := MvPolynomial (Fin s) K
  let : Algebra P A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral P A := ⟨hf⟩
  have hP : Ring.DimensionLEOne P := polynomial_dim K hs
  rw [Ring.krullDimLE_iff]
  have hdim : ringKrullDim A ≤ ringKrullDim P :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap P A)) (fun _ _ h =>
      Ideal.IsIntegral.comap_lt_comap h)
  exact hdim.trans (Ring.krullDimLE_iff.mp inferInstance)

/-- Every affine chart of a finite-type scheme with a dense smooth curve open has dimension at most one. -/
theorem chart_dimension {K : Type} [Field K] {X B : Scheme.{0}} [NoetherianSpace X]
    (j : X ⟶ B) [IsOpenImmersion j] [IsDominant j]
    (p : B ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p]
    [SmoothOfRelativeDimension 1 (j ≫ p)] {V : B.Opens} (hV : IsAffineOpen V) :
    Ring.KrullDimLE 1 Γ(B, V) := by
  let A := Γ(B, V)
  rcases subsingleton_or_nontrivial A with h | h
  · exact Ring.krullDimLE_iff.mpr (by rw [ringKrullDim_eq_bot_of_subsingleton]; exact bot_le)
  let hle : V ≤ p ⁻¹ᵁ ⊤ := by simp
  let c := (Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appLE ⊤ V hle
  let : Algebra K A := c.hom.toAlgebra
  let : Algebra.FiniteType K A := (p.finiteType_appLE (isAffineOpen_top _) hV hle).comp
    (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of K)).symm.commRingCatIsoToRingEquiv.surjective)
  obtain ⟨s, g, hg, hi⟩ := exists_integral_inj_algHom_of_fg K A
  apply dim_of_finite g hi
  by_contra! hs
  let Y := (j ⁻¹ᵁ V).toScheme
  let a : Y ⟶ Spec A := CycleQ2DenseOpenAffineSections.chart j hV
  let b := Spec.map (CommRingCat.ofHom g.toRingHom)
  let q := Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (Fin s) K))
  let px := (j ⁻¹ᵁ V).ι ≫ j ≫ p
  let : NoetherianSpace Y := NoetherianSpace.set (j ⁻¹ᵁ V : Set X)
  let : SmoothOfRelativeDimension 1 px := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 (j ⁻¹ᵁ V).ι (j ≫ p)
  let : SmoothOfRelativeDimension s q := affine_smooth K s
  have ha : DenseRange a := by
    have : IsDominant (j ∣_ V) := IsZariskiLocalAtTarget.restrict (P := @IsDominant) inferInstance V
    let : IsDominant a := by dsimp [a, CycleQ2DenseOpenAffineSections.chart]; infer_instance
    exact a.denseRange
  have hb : DenseRange b := by
    apply (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical g.toRingHom).mpr
    rw [(RingHom.injective_iff_ker_eq_bot g.toRingHom).mp hg]
    exact bot_le
  have hc : Spec.map c = hV.fromSpec ≫ p := by
    rw [Spec.map_comp, ← IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hV hle,
      IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv]
  have hbq : b ≫ q = Spec.map c := by
    rw [← Spec.map_comp]
    apply congrArg Spec.map
    apply CommRingCat.hom_ext
    exact RingHom.ext g.commutes
  have fac : (a ≫ b) ≫ q = px := by
    rw [Category.assoc, hbq, hc]
    change ((j ∣_ V) ≫ hV.isoSpec.hom) ≫ hV.fromSpec ≫ p = _
    simp only [IsAffineOpen.fromSpec, Iso.hom_inv_id_assoc, Category.assoc,
      morphismRestrict_ι_assoc, px]
  exact (closure_range_ne_univ 1 s hs px q (genericPolynomialPoint K s) (a ≫ b) fac)
    (denseRange_iff_closure_range.mp (hb.comp ha b.continuous))

/-- On an integral scheme of finite type over a field, a single nonempty smooth curve
open bounds the dimension of all affine charts. -/
theorem chart_dimension_of_nonempty_smooth_open {K : Type} [Field K] {B : Scheme.{0}}
    [IsIntegral B] (p : B ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p] [QuasiCompact p]
    (U : B.Opens) (hU : (U : Set B).Nonempty) [SmoothOfRelativeDimension 1 (U.ι ≫ p)]
    {V : B.Opens} (hV : IsAffineOpen V) : Ring.KrullDimLE 1 Γ(B, V) := by
  have : IsDominant U.ι := ⟨by
    change Dense (Set.range U.ι)
    simpa using U.isOpen.dense hU⟩
  have : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian p
  have : CompactSpace B := QuasiCompact.compactSpace_of_compactSpace p
  have : IsNoetherian B := ⟨⟩
  have : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set B)
  exact chart_dimension U.ι p hV

end CycleQ2CurveChartDimension

#print axioms CycleQ2CurveChartDimension.chart_dimension
#print axioms CycleQ2CurveChartDimension.chart_dimension_of_nonempty_smooth_open
