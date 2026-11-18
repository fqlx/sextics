import Proposal.GeometricLiteralSweptSupport
import Proposal.GeometricLiteralIncidenceRelativeCylinder
import Proposal.GeometricLiteralRelativeAmbientProper
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Dimension of the swept scheme over the sextic coefficients

Noether normalization on the swept scheme gives a finite dominant map
to affine space, dominated by the smooth incidence surface. This bounds
the dimension of the swept scheme on the fixed sextic and after an
arbitrary field-valued coefficient specialization.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralSweptDimensionUpper

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

private theorem chart_dimension {K : Type} [Field K] {X B : Scheme.{0}} [NoetherianSpace X]
    (n : ℕ) (j : X ⟶ B) [IsDominant j]
    (p : B ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p]
    [SmoothOfRelativeDimension n (j ≫ p)] {V : B.Opens} (hV : IsAffineOpen V) :
    Ring.KrullDimLE n Γ(B, V) := by
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
  have mono : ringKrullDim A ≤ ringKrullDim (MvPolynomial (Fin s) K) := by
    let P := MvPolynomial (Fin s) K
    let : Algebra P A := g.toRingHom.toAlgebra
    let : Algebra.IsIntegral P A := ⟨hi⟩
    exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap P A))
      (fun _ _ h => Ideal.IsIntegral.comap_lt_comap h)
  have hfield : ringKrullDim K = 0 := Order.krullDim_eq_zero_of_unique
  have polynomial_bound : ringKrullDim (MvPolynomial (Fin s) K) = s := by
    simp [MvPolynomial.ringKrullDim_of_isNoetherianRing, hfield, Nat.card_eq_fintype_card]
  apply Ring.krullDimLE_iff.mpr
  rw [polynomial_bound] at mono
  refine mono.trans ?_
  suffices h : s ≤ n by exact_mod_cast h
  by_contra! hs
  let Y := (j ⁻¹ᵁ V).toScheme
  let a : Y ⟶ Spec A := (j ∣_ V) ≫ hV.isoSpec.hom
  let b := Spec.map (CommRingCat.ofHom g.toRingHom)
  let q := Spec.map (CommRingCat.ofHom (MvPolynomial.C : K →+* MvPolynomial (Fin s) K))
  let px := (j ⁻¹ᵁ V).ι ≫ j ≫ p
  let : NoetherianSpace Y := NoetherianSpace.set (j ⁻¹ᵁ V : Set X)
  let : SmoothOfRelativeDimension n px := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 n (j ⁻¹ᵁ V).ι (j ≫ p)
  let : SmoothOfRelativeDimension s q := affine_smooth K s
  have ha : DenseRange a := by
    have : IsDominant (j ∣_ V) := IsZariskiLocalAtTarget.restrict (P := @IsDominant) inferInstance V
    let : IsDominant a := by dsimp [a]; infer_instance
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
  exact (closure_range_ne_univ n s hs px q (genericPolynomialPoint K s) (a ≫ b) fac)
    (denseRange_iff_closure_range.mp (hb.comp ha b.continuous))

private theorem image_chart {K : Type} [Field K] {X Y : Scheme.{0}} [NoetherianSpace X]
    (f : X ⟶ Y) (p : Y ⟶ Spec (CommRingCat.of K)) [LocallyOfFiniteType p]
    (hs : SmoothOfRelativeDimension 2 (f ≫ p))
    {W : f.image.Opens} (hW : IsAffineOpen W) : Ring.KrullDimLE 2 Γ(f.image,W) := by
  let : SmoothOfRelativeDimension 2 (f.toImage ≫ f.imageι ≫ p) := by simpa using hs
  exact chart_dimension 2 f.toImage (f.imageι ≫ p) hW

open CategoryTheory.Limits CycleQ2IncidenceEtaleParameter CycleQ2IncidenceTimeCurve
  CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralAbelJacobiTimeFamily
  CycleQ2LiteralAbelJacobiTimeProjection CycleQ2LiteralIncidenceCylinderMap
  CycleQ2LiteralIncidenceRelativeCylinder CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2IncidenceSeedFiberCover CycleQ2GeometricIncidenceProj

theorem fixed_chart (V : parameterScheme.Opens) (t : Fin 3 → ℂ)
    (hs : SmoothOfRelativeDimension 2 (projection V t ≫ (timeOpen V).ι ≫ toComplex))
    (hp : IsProper (projection V t)) {W : (q V t).image.Opens} (hW : IsAffineOpen W) :
    Ring.KrullDimLE 2 Γ((q V t).image, W) := by
  let := smooth_parameter_curve
  let : Smooth toComplex := SmoothOfRelativeDimension.smooth 1 _
  let : IsNoetherian Curve := { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian toComplex }
  let : CompactSpace (timeOpen V).toScheme := isCompact_iff_compactSpace.mp
    (NoetherianSpace.isCompact ((timeOpen V : Curve.Opens) : Set Curve))
  let := QuasiCompact.compactSpace_of_compactSpace (projection V t)
  let : Smooth (projection V t ≫ (timeOpen V).ι ≫ toComplex) := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian (family V t) :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
        (projection V t ≫ (timeOpen V).ι ≫ toComplex) }
  let := CycleQ2LiteralAmbientCylinder.fixed_proper
  exact image_chart (q V t) (pullback.fst seedSextic universalAmbientToBase)
    ((q_overComplex V t).symm ▸ hs) hW

/-- One marked section neighborhood bounds the swept support on every field-valued
coefficient fibre, including the generic monic sextic. -/
theorem coefficient_surface (t : Fin 3 → ℂ) (hi : AlgebraicIndependent ℚ t) :
    ∃ V : parameterScheme.Opens, seedBasePoint ∈ V ∧
      ∀ (K : Type) [Field K] (i : Spec (CommRingCat.of K) ⟶ sexticBase),
        Surjective (curveMap i V t) ∧ SmoothOfRelativeDimension 2 (curveMap i V t ≫ timeMap i V) ∧
        ∀ (W : (relativeQ i V t).image.Opens), IsAffineOpen W →
          Ring.KrullDimLE 2 Γ((relativeQ i V t).image, W) := by
  obtain ⟨V, hV, hc, hp, hsurj⟩ :=
    CycleQ2LiteralAbelJacobiSeedLiftDimension.dimension_one_neighborhood_of_seedMinorCover t
      (CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t hi)
  refine ⟨V, hV, ?_⟩
  intro K _ i
  let : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension 1) :=
    smoothOfRelativeDimension_isStableUnderBaseChange 1
  let : SmoothOfRelativeDimension 1 (curveMap i V t) := MorphismProperty.pullback_fst _ _ hc
  let := timeMap_smooth i V
  let : IsProper (curveMap i V t) := MorphismProperty.pullback_fst _ _ hp
  let := CycleQ2RelativeRegularSection.parameter_noetherian
  let : NoetherianSpace parameterScheme :=
    inferInstanceAs (NoetherianSpace (Spec (CommRingCat.of ParameterAlgebra)))
  let : NoetherianSpace V.toScheme := NoetherianSpace.set (V : Set parameterScheme)
  let : QuasiCompact (timeMap i V) :=
    inferInstanceAs (QuasiCompact (pullback.fst i (V.ι ≫ parameterToSextics)))
  let := QuasiCompact.compactSpace_of_compactSpace (timeMap i V)
  let := QuasiCompact.compactSpace_of_compactSpace (curveMap i V t)
  have hs := smoothOfRelativeDimension_comp 1 1 (curveMap i V t) (timeMap i V)
  let : Surjective ((CycleQ2RelativeConstantCurve.relativeCurveToBase
      CycleQ2IncidenceEtaleParameter.incidencePoint t) ∣_ V) := ⟨hsurj⟩
  refine ⟨(by unfold curveMap; infer_instance), hs, ?_⟩
  intro W hW
  let : Smooth (curveMap i V t ≫ timeMap i V) := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian (Surface i V t) :=
    { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian (curveMap i V t ≫ timeMap i V) }
  let := CycleQ2LiteralRelativeAmbientProper.ambient_proper i
  exact image_chart (relativeQ i V t) (pullback.fst i universalAmbientToBase)
    ((relativeQ_fst i V t).symm ▸ hs) hW

end CycleQ2LiteralSweptDimensionUpper
end

#print axioms CycleQ2LiteralSweptDimensionUpper.fixed_chart
#print axioms CycleQ2LiteralSweptDimensionUpper.coefficient_surface
