import Proposal.GeometricLiteralTimeNormalizationFinite
import Proposal.GeometricSmoothImageDimension

/-!
# Dimension at the boundary of the proper time base

Noether normalization of an affine chart gives a finite dominant map to
affine space. The original smooth time open is dense, so comparison of
dimensions bounds the number of polynomial coordinates by one. This
also applies to every affine chart of the finite normalization.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeCurveDimension

open CategoryTheory AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralTimeCurveCompletion
  CycleQ2LiteralTimeCurveNormalization CycleQ2SweptSupport

private def affinePresentation (s : ℕ) :
    Algebra.PreSubmersivePresentation ℂ (MvPolynomial (Fin s) ℂ) (Fin s) Empty where
  toPresentation :=
    { toGenerators := Algebra.Generators.mvPolynomial ℂ (Fin s)
      relation := Empty.elim
      span_range_relation_eq_ker := by rw [Algebra.Generators.ker_mvPolynomial]; simp }
  map := Empty.elim
  map_inj := by intro a; exact a.elim

private theorem affine_smooth (s : ℕ) : SmoothOfRelativeDimension s
    (Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial (Fin s) ℂ))) := by
  let P : Algebra.SubmersivePresentation ℂ (MvPolynomial (Fin s) ℂ) (Fin s) Empty :=
    { toPreSubmersivePresentation := affinePresentation s
      jacobian_isUnit := by
        rw [Algebra.PreSubmersivePresentation.jacobian_eq_jacobiMatrix_det,
          Matrix.det_isEmpty, map_one]
        exact isUnit_one }
  have hs : Algebra.IsStandardSmoothOfRelativeDimension s ℂ (MvPolynomial (Fin s) ℂ) :=
    P.isStandardSmoothOfRelativeDimension (by
      change Nat.card (Fin s) - Nat.card Empty = s
      simp [Nat.card_eq_fintype_card])
  apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension s)).mpr
  exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _
    ((RingHom.isStandardSmoothOfRelativeDimension_algebraMap s).mpr hs)

private theorem polynomial_dim {s : ℕ} (hs : s ≤ 1) :
    Ring.DimensionLEOne (MvPolynomial (Fin s) ℂ) := by
  interval_cases s
  · exact Ring.DimensionLEOne.of_ringEquiv (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0))
  · exact Ring.DimensionLEOne.of_ringEquiv (MvPolynomial.uniqueAlgEquiv ℂ (Fin 1)).toRingEquiv

private theorem dim_of_finite {s : ℕ} {A : Type} [CommRing A] [Algebra ℂ A]
    (g : MvPolynomial (Fin s) ℂ →ₐ[ℂ] A) (hf : g.IsIntegral) (hs : s ≤ 1) :
    Ring.KrullDimLE 1 A := by
  let P := MvPolynomial (Fin s) ℂ
  let : Algebra P A := g.toRingHom.toAlgebra
  let : Algebra.IsIntegral P A := ⟨hf⟩
  have hP : Ring.DimensionLEOne P := polynomial_dim hs
  rw [Ring.krullDimLE_iff]
  have hdim : ringKrullDim A ≤ ringKrullDim P :=
    Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap P A)) (fun _ _ h =>
      Ideal.IsIntegral.comap_lt_comap h)
  exact hdim.trans (Ring.krullDimLE_iff.mp inferInstance)

private theorem chart_dimension {X B : Scheme.{0}} [NoetherianSpace X]
    (j : X ⟶ B) [IsOpenImmersion j] [IsDominant j]
    (p : B ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType p]
    [SmoothOfRelativeDimension 1 (j ≫ p)] {V : B.Opens} (hV : IsAffineOpen V) :
    Ring.KrullDimLE 1 Γ(B, V) := by
  let A := Γ(B, V)
  rcases subsingleton_or_nontrivial A with h | h
  · exact Ring.krullDimLE_iff.mpr (by rw [ringKrullDim_eq_bot_of_subsingleton]; exact bot_le)
  let hle : V ≤ p ⁻¹ᵁ ⊤ := by simp
  let c := (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ p.appLE ⊤ V hle
  let : Algebra ℂ A := c.hom.toAlgebra
  let : Algebra.FiniteType ℂ A := (p.finiteType_appLE (isAffineOpen_top _) hV hle).comp
    (RingHom.FiniteType.of_surjective _
      (Scheme.ΓSpecIso (CommRingCat.of ℂ)).symm.commRingCatIsoToRingEquiv.surjective)
  obtain ⟨s, g, hg, hi⟩ := exists_integral_inj_algHom_of_fg ℂ A
  apply dim_of_finite g hi
  by_contra! hs
  let Y := (j ⁻¹ᵁ V).toScheme
  let a : Y ⟶ Spec A := CycleQ2DenseOpenAffineSections.chart j hV
  let b := Spec.map (CommRingCat.ofHom g.toRingHom)
  let q := Spec.map (CommRingCat.ofHom (MvPolynomial.C : ℂ →+* MvPolynomial (Fin s) ℂ))
  let px := (j ⁻¹ᵁ V).ι ≫ j ≫ p
  let : NoetherianSpace Y := NoetherianSpace.set (j ⁻¹ᵁ V : Set X)
  let : SmoothOfRelativeDimension 1 px := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 (j ⁻¹ᵁ V).ι (j ≫ p)
  let : SmoothOfRelativeDimension s q := affine_smooth s
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
  exact (closure_range_ne_univ 1 s hs px q (genericPolynomialPoint ℂ s) (a ≫ b) fac)
    (denseRange_iff_closure_range.mp (hb.comp ha b.continuous))

theorem completion_chart (U : Curve.Opens) {V : (Completion U).Opens} (hV : IsAffineOpen V) :
    Ring.KrullDimLE 1 Γ(Completion U, V) := by
  let : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set Curve)
  let : SmoothOfRelativeDimension 1 (inclusion U ≫ structureMap U) := by
    rw [CycleQ2LiteralTimeCurveCompletion.inclusion_over]
    let := smooth_parameter_curve
    exact smoothOfRelativeDimension_comp 0 1 _ _
  exact chart_dimension (inclusion U) (structureMap U) hV

theorem normalization_chart (U : Curve.Opens) {V : (Normalization U).Opens} (hV : IsAffineOpen V) :
    Ring.KrullDimLE 1 Γ(Normalization U, V) := by
  let : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set Curve)
  let := smooth_on_original_open U
  exact chart_dimension (openInclusion U) (toComplexPoint U) hV

end CycleQ2LiteralTimeCurveDimension
end

#print axioms CycleQ2LiteralTimeCurveDimension.completion_chart
#print axioms CycleQ2LiteralTimeCurveDimension.normalization_chart
