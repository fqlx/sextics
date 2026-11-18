import Proposal.GeometricLiteralAbelJacobiQChart
import Proposal.GeometricLiteralThreefoldVertexMotion
import Proposal.GeometricLiteralAbelJacobiTimeContraction
import Proposal.GeometricLiteralSweptSupport
import Proposal.GeometricLiteralIncidenceRelativeNormalization
import Mathlib.RingTheory.KrullDimension.Zero

/-!
# Lower dimension of the swept image on a chart with nonzero normal

The open part of the seed curve where the marked cubic has nonzero normal
contains a nonclosed point. Its preimage in the swept chart cannot be a
minimal prime. At a minimal prime in a reduced ring the cubic would vanish
after multiplication by an element outside that prime. The first-order
family differentiates this identity to the product of that element and
the nonzero cubic normal.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralSweptDimension

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open CycleQ2LiteralAbelJacobiTimeProjection CycleQ2LiteralAbelJacobiTimeFamily
  CycleQ2IncidenceEtaleParameter CycleQ2IncidenceSeedFiberCover CycleQ2LiteralIncidenceCylinderMap
  CycleQ2LiteralAbelJacobiQChart CycleQ2LiteralAmbientCylinder CycleQ2LiteralAbelJacobiTimeCharts
  CycleQ2LiteralAmbientCharts CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAbelJacobiMovingNormal
  CycleQ2LiteralAbelJacobiRelativeNormal CycleQ2LiteralCylinderEvaluation
  CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralIncidenceTimeCurve

open scoped DualNumber

attribute [local instance] CycleQ2IncidenceSeedFiber.seedAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderAlgebra
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderModule
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderSMul
  CycleQ2FirstOrderTensorReduction.parameterFirstOrderTower
  thickCommRing fixedCommRing seedChartCommRing closedAlgebra fixedAlgebra fixedTower fixedSeedTower
  CycleQ2CurveParameterTangent.chartComplexAlgebra
  familyAlgebra familyComplexTower reductionAlgebra fixedCurveTower familyReductionTower

private theorem generic_line_not_closed :
    ¬ IsClosed ({CycleQ2SweptSupport.genericPolynomialPoint ℂ 1} :
      Set (CycleQ2SweptSupport.affineSpace ℂ 1)) := by
  intro h
  have hm : (⊥ : Ideal (MvPolynomial (Fin 1) ℂ)).IsMaximal :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mp h
  have hf := Ring.isField_iff_maximal_bot.mpr hm
  obtain ⟨y, hy⟩ := hf.mul_inv_cancel (MvPolynomial.X_ne_zero (R := ℂ) (0 : Fin 1))
  simpa using congrArg (MvPolynomial.eval (fun _ : Fin 1 => (0 : ℂ))) hy

private theorem nonmaximal_in_basicOpen {R : Type} [CommRing R] [Algebra ℂ R]
    (hs : SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap ℂ R))))
    [_root_.IsReduced R] {a : R} (ha : a ≠ 0) :
    ∃ p : PrimeSpectrum R, a ∉ p.asIdeal ∧ ¬ p.asIdeal.IsMaximal := by
  let f := Spec.map (CommRingCat.ofHom (algebraMap ℂ R))
  let U : (Spec (CommRingCat.of R)).Opens := PrimeSpectrum.basicOpen a
  have hU : U ≠ ⊥ := fun he => ha ((PrimeSpectrum.basicOpen_eq_bot_iff _).mp he).eq_zero
  obtain ⟨x, hx⟩ := U.ne_bot_iff_nonempty.mp hU
  haveI : SmoothOfRelativeDimension 1 (U.ι ≫ f) := smoothOfRelativeDimension_comp 0 1 _ _
  obtain ⟨S, j, hj, _, g, hg, _, z, hz⟩ :=
    CycleQ2SweptSupport.exists_etale_chart 1 (U.ι ≫ f) ⟨x, hx⟩
  refine ⟨U.ι (j z), (j z).2, fun hmax => generic_line_not_closed ?_⟩
  have hclosed : IsClosed ({U.ι (j z)} : Set (Spec (CommRingCat.of R))) :=
    (PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr hmax
  have hzClosed : z ∈ closedPoints (Spec S) :=
    preimage_closedPoints_subset (j ≫ U.ι).isOpenEmbedding.injective (j ≫ U.ι).continuous hclosed
  have h := g.closePoints_subset_preimage_closedPoints hzClosed
  change IsClosed ({g z} : Set (CycleQ2SweptSupport.affineSpace ℂ 1)) at h
  rwa [← hz]

private theorem annihilator_outside {R : Type} [CommRing R] [_root_.IsReduced R]
    {p : Ideal R} (hp : p ∈ minimalPrimes R) {x : R} (hx : x ∈ p) :
    ∃ s ∉ p, s * x = 0 := by
  have : p.IsPrime := hp.1.1
  let L := Localization.AtPrime p
  have : Ring.KrullDimLE 0 L := Ring.KrullDimLE.of_isLocalization p hp L
  have hf : IsField L := Ring.KrullDimLE.isField_of_isReduced
  have hz : algebraMap R L x = 0 := by
    have hm := (IsLocalization.AtPrime.to_map_mem_maximal_iff L p x).mpr hx
    rwa [IsLocalRing.isField_iff_maximalIdeal_eq.mp hf, Ideal.mem_bot] at hm
  have h := (IsLocalization.eq_iff_exists p.primeCompl L).mp
    (show algebraMap R L x = algebraMap R L 0 by simpa using hz)
  obtain ⟨s, hs⟩ := h
  exact ⟨s, s.property, by simpa [mul_comm] using hs⟩

variable (V : parameterScheme.Opens) (t : Fin 3 → ℂ) (i : Fin 4)

def fixedChart : Spec (CommRingCat.of (T i)) ⟶ FixedThreefold :=
  chartInclusion i ≫ fixedIso.inv

instance : IsOpenImmersion (fixedChart i) := by unfold fixedChart; infer_instance

/-- The actual affine open of the scheme-theoretic swept image over the original fixed chart. -/
abbrev sweptChart := pullback (fixedChart i) (q V t).imageι

abbrev coordinateRing := Γ(sweptChart V t i, ⊤)

private def thickToSwept (hV : seedBasePoint ∈ V) :
    Spec (CommRingCat.of (B t i)) ⟶ sweptChart V t i :=
  pullback.lift (Spec.map (CommRingCat.ofHom (toFamily t i)))
    (thickChart V t hV i ≫ (q V t).toImage) (by
      rw [Category.assoc, Scheme.Hom.toImage_imageι]
      apply (cancel_mono fixedIso.hom).mp
      simp only [fixedChart, Category.assoc, Iso.inv_hom_id, Category.comp_id,
        thickChart_toSmoothThreefold])

private def fromFixed : CommRingCat.of (T i) ⟶ coordinateRing V t i :=
  Spec.preimage ((sweptChart V t i).isoSpec.inv ≫ pullback.fst _ _)

private def toThick (hV : seedBasePoint ∈ V) : coordinateRing V t i ⟶ CommRingCat.of (B t i) :=
  Spec.preimage (thickToSwept V t i hV ≫ (sweptChart V t i).isoSpec.hom)

private theorem thick_factor (hV : seedBasePoint ∈ V) :
    fromFixed V t i ≫ toThick V t i hV = CommRingCat.ofHom (toFamily t i) := by
  apply Spec.map_injective
  rw [Spec.map_comp, fromFixed, toThick, Spec.map_preimage, Spec.map_preimage]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, thickToSwept, pullback.lift_fst]

private theorem coordinate_reduced
    (hs : SmoothOfRelativeDimension 2 (projection V t ≫ (timeOpen V).ι ≫ toComplex))
    (hp : IsProper (projection V t)) : _root_.IsReduced (coordinateRing V t i) := by
  let := smooth_parameter_curve
  let : Smooth toComplex := SmoothOfRelativeDimension.smooth 1 _
  let : IsNoetherian Curve := { toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian toComplex }
  let : CompactSpace (timeOpen V).toScheme := isCompact_iff_compactSpace.mp
    (NoetherianSpace.isCompact ((timeOpen V : Curve.Opens) : Set Curve))
  let : Smooth (projection V t ≫ (timeOpen V).ι ≫ toComplex) := SmoothOfRelativeDimension.smooth 2 _
  let : IsNoetherian (family V t) := {
    toIsLocallyNoetherian := LocallyOfFiniteType.isLocallyNoetherian
      (projection V t ≫ (timeOpen V).ι ≫ toComplex)
    toCompactSpace := QuasiCompact.compactSpace_of_compactSpace (projection V t) }
  let : AlgebraicGeometry.IsReduced (family V t) :=
    CycleQ2LiteralIncidenceRelativeNormalization.reduced_of_smooth_over_domain 2
      (projection V t ≫ (timeOpen V).ι ≫ toComplex)
  let f := q V t
  let : AlgebraicGeometry.IsReduced f.image := by
    apply (AlgebraicGeometry.IsReduced.iff_of_openCover (X := f.image) f.ker.subschemeCover.openCover).mpr
    change ∀ U : FixedThreefold.affineOpens, AlgebraicGeometry.IsReduced
      (Spec (CommRingCat.of (Γ(FixedThreefold, U.1) ⧸ f.ker.ideal U)))
    intro U
    apply (affine_isReduced_iff _).mpr
    let : _root_.IsReduced Γ(f.image, f.imageι ⁻¹ᵁ U.1) :=
      isReduced_of_injective (f.toImage.app _).hom (f.toImage_app_injective U)
    exact isReduced_of_injective (f.ker.subschemeObjIso U).inv.hom
      (f.ker.subschemeObjIso U).symm.commRingCatIsoToRingEquiv.injective
  let : AlgebraicGeometry.IsReduced (sweptChart V t i) :=
    isReduced_of_isOpenImmersion (pullback.snd (fixedChart i) f.imageι)
  infer_instance

private theorem lower_of_derivative {R A B : Type} [CommRing R] [CommRing A] [CommRing B]
    [Algebra ℂ A] [Algebra ℂ B] [Algebra B A] [IsScalarTower ℂ B A] [_root_.IsReduced R]
    (b : R →+* B) (D : Derivation ℂ B A) (u : R)
    (hs : Function.Surjective ((algebraMap B A).comp b)) (hu : algebraMap B A (b u) = 0)
    (p : PrimeSpectrum A) (hpm : ¬p.asIdeal.IsMaximal) (hp : D (b u) ∉ p.asIdeal) :
    1 < ringKrullDim R := by
  by_contra! hdim
  have hd : Ring.KrullDimLE 1 R := Ring.krullDimLE_iff.mpr (by simpa using hdim)
  let ρ := (algebraMap B A).comp b
  let P := p.asIdeal.comap ρ
  have hP : P.IsPrime := Ideal.comap_isPrime ρ p.asIdeal
  have hn : ¬P.IsMaximal := by
    intro h
    have hf := Ideal.map_eq_top_or_isMaximal_of_surjective ρ hs h
    rw [show P.map ρ = p.asIdeal from Ideal.map_comap_of_surjective ρ hs _] at hf
    exact hpm (hf.resolve_left p.isPrime.ne_top)
  have hmin := (Ring.krullDimLE_one_iff.mp hd P hP).resolve_right hn
  have huP : u ∈ P := by change algebraMap B A (b u) ∈ p.asIdeal; rw [hu]; exact p.asIdeal.zero_mem
  obtain ⟨s, hsp, hsu⟩ := annihilator_outside hmin huP
  have he := congrArg D (show b s * b u = 0 by rw [← map_mul, hsu, map_zero])
  rw [D.leibniz, map_zero, Algebra.smul_def, Algebra.smul_def, hu, zero_mul, add_zero] at he
  exact (p.isPrime.mem_or_mem (he ▸ p.asIdeal.zero_mem)).elim hsp hp

theorem seed_chart_smooth (hi : AlgebraicIndependent ℚ t) :
    SmoothOfRelativeDimension 1 (Spec.map (CommRingCat.ofHom (algebraMap ℂ (A t i)))) := by
  let seed := CycleQ2SeedConeSection.seed
  have hs := CycleQ2LiteralAbelJacobiSeedLiftDimension.smooth_seed_of_seedMinorCover t
    (CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t hi)
  let j := (CycleQ2SpecializedCurveCoordinateChart.specializedCoordinateAffineChart seed t i).inv ≫
    (CycleQ2SpecializedCurveCoordinateChart.specializedCoordinatePatch seed t i).ι
  have : IsOpenImmersion j := by dsimp [j]; infer_instance
  have hc : SmoothOfRelativeDimension 1 (j ≫ CycleQ2SpecializedProjectiveCurve.specializedCurveToBase seed t) :=
    smoothOfRelativeDimension_comp 0 1 _ _
  dsimp only [j] at hc
  rw [Category.assoc, CycleQ2SpecializedCurveCoordinateChart.specializedCoordinateAffineChart_overBase] at hc
  exact hc

/-- On the original smooth seed chart, the principal open cut out by the
infinitesimal cubic coefficient contains a nonclosed point. -/
theorem normal_locus_point (hi : AlgebraicIndependent ℚ t) [Module.Flat (DualNumber ℂ) (B t i)]
    (hn : relativeNormal t i ((idealOnT t i).toCotangent (cubicClass t i)) ≠ 0) :
    ∃ p : PrimeSpectrum (A t i), p ∈ PrimeSpectrum.basicOpen (-(seedChartMap t i (tangentL i))) ∧
      ¬p.asIdeal.IsMaximal := by
  have hcurve := seed_chart_smooth t i hi
  let : _root_.IsReduced (A t i) :=
    CycleQ2LiteralAbelJacobiSeedLiftRegular.reduced_of_smoothDimension 1 _
      ((HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)).mp hcurve)
  rw [relativeNormal_cubic] at hn
  exact nonmaximal_in_basicOpen hcurve hn

/-- The nonzero cubic normal forces the affine patch of the actual swept
scheme-theoretic image meeting its nonvanishing locus to have dimension at least two. -/
theorem lower_at_normal (hi : AlgebraicIndependent ℚ t) (hV : seedBasePoint ∈ V)
    (hs : SmoothOfRelativeDimension 2 (projection V t ≫ (timeOpen V).ι ≫ toComplex))
    (hp : IsProper (projection V t)) [Module.Flat (DualNumber ℂ) (B t i)]
    (hn : relativeNormal t i ((idealOnT t i).toCotangent (cubicClass t i)) ≠ 0) :
    1 < ringKrullDim (coordinateRing V t i) := by
  let := coordinate_reduced V t i hs hp
  have : Algebra.FormallySmooth ℂ (A t i) := by
    have := CycleQ2LiteralAbelJacobiSmoothNormal.seedChart_smooth_of_minors t
      (CycleQ2LiteralAbelJacobiBertiniMinor.prime_minor_of_independent t hi) i
    infer_instance
  obtain ⟨p, hp', hpm⟩ := normal_locus_point t i hi hn
  obtain ⟨v, hv, _⟩ := exists_evaluation t i
  let c := (fromFixed V t i).hom
  let b := (toThick V t i hV).hom
  have hcomp (a : T i) : b (c a) = toFamily t i a :=
    congrArg (fun g : CommRingCat.of (T i) ⟶ CommRingCat.of (B t i) => g.hom a) (thick_factor V t i hV)
  have hred (a : T i) : algebraMap (B t i) (A t i) (b (c a)) = toCurve t i a := by
    rw [hcomp]
    exact (IsScalarTower.algebraMap_apply (T i) (B t i) (A t i) a).symm
  refine lower_of_derivative b v (c (cubicOnT i)) ?_ ?_ p hpm ?_
  · intro a
    obtain ⟨g, hg⟩ := toCurve_surjective t i a
    exact ⟨c g, (hred g).trans hg⟩
  · exact (hred _).trans (cubicOnT_zero t i)
  · rw [hcomp, CycleQ2LiteralThreefoldVertexMotion.chart_velocity_cubic t i v hv]
    exact hp'

/-- For every independent choice of the section coefficients there is an
actual marked normal chart of the swept image of dimension at least two. -/
theorem exists_swept_chart (hi : AlgebraicIndependent ℚ t) :
    ∃ (V : parameterScheme.Opens) (_ : seedBasePoint ∈ V) (j : Fin 3),
      1 < ringKrullDim (coordinateRing V t j.succ) := by
  obtain ⟨V, hV, _, _, hs, hp, _, _, hf, j, hnormal⟩ := time_family_of_independent t hi
  let := hf j.succ
  exact ⟨V, hV, j, lower_at_normal V t j.succ hi hV hs hp hnormal⟩

/-- The marked swept chart contains a two-step specialization chain, starting
at a component's generic point and ending at a closed point. -/
theorem exists_swept_prime_chain (hi : AlgebraicIndependent ℚ t) :
    ∃ (V : parameterScheme.Opens) (_ : seedBasePoint ∈ V) (j : Fin 3)
      (P Q M : Ideal (coordinateRing V t j.succ)),
      P ∈ minimalPrimes _ ∧ Q.IsPrime ∧ M.IsMaximal ∧ P < Q ∧ Q < M := by
  obtain ⟨V, hV, j, hd⟩ := exists_swept_chart t hi
  let R := coordinateRing V t j.succ
  have hn : ¬ Ring.KrullDimLE 1 R := fun h =>
    hd.not_ge (by simpa using Ring.krullDimLE_iff.mp h)
  rw [Ring.krullDimLE_one_iff] at hn
  push Not at hn
  obtain ⟨Q, hQ, hmin, hmax⟩ := hn
  obtain ⟨P, hP, hPQ⟩ := Ideal.exists_minimalPrimes_le (bot_le : (⊥ : Ideal R) ≤ Q)
  obtain ⟨M, hM, hQM⟩ := Q.exists_le_maximal hQ.ne_top
  exact ⟨V, hV, j, P, Q, M, hP, hQ, hM,
    hPQ.lt_of_ne (fun e => hmin (e ▸ hP)), hQM.lt_of_ne (fun e => hmax (e.symm ▸ hM))⟩

/-- The chart maps openly into the original swept image, so its lower dimension
bound also holds on that image. -/
theorem chart_le_swept :
    ringKrullDim (coordinateRing V t i) ≤ topologicalKrullDim (q V t).image := by
  calc
    ringKrullDim (coordinateRing V t i) =
        topologicalKrullDim (Spec (coordinateRing V t i)) :=
      (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _).symm
    _ = topologicalKrullDim (sweptChart V t i) :=
      (IsHomeomorph.topologicalKrullDim_eq _
        (sweptChart V t i).isoSpec.hom.homeomorph.isHomeomorph).symm
    _ ≤ topologicalKrullDim (q V t).image :=
      (pullback.snd (fixedChart i) (q V t).imageι).isOpenEmbedding.isInducing.topologicalKrullDim_le

theorem exists_swept_dimension (hi : AlgebraicIndependent ℚ t) :
    ∃ (V : parameterScheme.Opens) (_ : seedBasePoint ∈ V), 1 < topologicalKrullDim (q V t).image := by
  obtain ⟨V, hV, j, hdim⟩ := exists_swept_chart t hi
  exact ⟨V, hV, hdim.trans_le (chart_le_swept V t j.succ)⟩

end CycleQ2LiteralSweptDimension
end

#print axioms CycleQ2LiteralSweptDimension.exists_swept_chart

#print axioms CycleQ2LiteralSweptDimension.exists_swept_prime_chain

#print axioms CycleQ2LiteralSweptDimension.exists_swept_dimension
