import Proposal.GeometricLiteralAbelJacobiSeedLiftPoints
import Proposal.GeometricSeedSectionInvertible

/-!
# Reading the three literal surface charts at primes of the section curve

The original map from the specialized curve to the literal surface pulls
the three selected weight-one opens back to the corresponding curve charts.
On each chart, membership in the basic open of a degree-zero section is
equivalent to nonmembership of its image in the affine curve prime.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralResidueRowPoint

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace MvPolynomial
open CycleQ2SeedProjectiveImageCocycle CycleQ2SeedProjectiveImageChart
  CycleQ2SeedSectionCurveRows CycleQ2SeedSectionSheafCurveBinding CycleQ2SeedSectionInvertible
  CycleQ2GeometricSurfaceAdjunction CycleQ2RelativeCurveChart CycleQ2FirstOrderCurveChartFlat
  CycleQ2SpecializedCurveCoordinateChart CycleQ2SpecializedProjectiveCurve
  CycleQ2IncidenceDehomogenizedChart CycleQ2GeometricIncidenceProj
  CycleQ2LiteralAbelJacobiSeedLiftPoints

attribute [local instance] CycleQ2RelativeCurveChartFiber.seedCurveChartCommRing
  CycleQ2SpecializedCurveCoordinateChart.specializedCoordinateCommRing
  CycleQ2SpecializedProjectiveCurve.nativePointSurfaceCommRing
  CycleQ2SpecializedProjectiveCurve.nativeSpecializedCurveCommRing
  CycleQ2RelativeCurveChart.coordinateRingCommRing

variable (t : Fin 3 → ℂ) (i : Fin 3)

theorem exists_literalChart_prime (x : specializedCurve seed t) :
    ∃ (i : Fin 3) (z : PrimeSpectrum (AffineCurveChart seed t i.succ)),
      seedChartToCurve t i.succ z = x := by
  have hc : curveToSurface t x ∈ ⨆ j : Fin 3, Patch j := by rw [CycleQ2SeedSectionSheafGlobal.patch_cover]; trivial
  obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hc
  have hx : x ∈ specializedCoordinatePatch seed t j.succ := by
    rw [← curveToSurface_preimage_patch]
    exact hj
  let u : (specializedCoordinatePatch seed t j.succ).toScheme := ⟨x, hx⟩
  refine ⟨j, (specializedCoordinateAffineChart seed t j.succ).hom u, ?_⟩
  change (specializedCoordinatePatch seed t j.succ).ι
    (((specializedCoordinateAffineChart seed t j.succ).hom ≫
      (specializedCoordinateAffineChart seed t j.succ).inv) u) = x
  rw [Iso.hom_inv_id]
  rfl

private theorem chart_section_prime (u : (specializedCoordinatePatch seed t i.succ).toScheme)
    (b : SpecializedCoordinateRing seed t i.succ) :
    (specializedCoordinatePatch seed t i.succ).ι u ∈
        (specializedCurve seed t).basicOpen (curveCoordinateSectionsEquiv t i b) ↔
      specializedCoordinateChartEquiv seed t i.succ b ∉
        ((specializedCoordinateAffineChart seed t i.succ).hom u).asIdeal := by
  let U := specializedCoordinatePatch seed t i.succ
  have h := congrArg (fun W : U.toScheme.Opens => u ∈ W)
    (U.toSpecΓ_preimage_basicOpen (curveCoordinateSectionsEquiv t i b))
  change (curveCoordinateSectionsEquiv t i b ∉ (U.toSpecΓ u).asIdeal) =
    (U.ι u ∈ (specializedCurve seed t).basicOpen (curveCoordinateSectionsEquiv t i b)) at h
  rw [← h]
  change _ ↔ curveCoordinateSectionsEquiv t i ((specializedCoordinateChartEquiv seed t i.succ).symm
    (specializedCoordinateChartEquiv seed t i.succ b)) ∉ (U.toSpecΓ u).asIdeal
  rw [AlgEquiv.symm_apply_apply]

/-- Test any degree-zero function from the original seed coordinate ring
on the literal surface by contracting an actual affine curve prime. -/
theorem mem_basicOpen_iff (z : PrimeSpectrum (AffineCurveChart seed t i.succ))
    (a : CoordinateRing seed i.succ) :
    curveToSurface t (seedChartToCurve t i.succ z) ∈
        Surface.basicOpen (seedCoordinateSectionsEquiv i a) ↔
      Ideal.Quotient.mk (affineSectionIdeal seed t i.succ)
        (familyCoordinateChartEquiv seed i.succ a) ∉ z.asIdeal := by
  let U := specializedCoordinatePatch seed t i.succ
  let e := specializedCoordinateAffineChart seed t i.succ
  let u := e.inv z
  let s := seedCoordinateSectionsEquiv i a
  have h : (specializedCurve seed t).basicOpen (curveChartSectionMap t i s) =
      U ⊓ (curveToSurface t ⁻¹ᵁ Surface.basicOpen s) :=
    Scheme.basicOpen_appLE (curveToSurface t) U (Patch i) _ s
  have hz : e.hom u = z := by
    change (e.inv ≫ e.hom) z = z
    rw [Iso.inv_hom_id]
    rfl
  calc
    _ ↔ U.ι u ∈ (specializedCurve seed t).basicOpen (curveChartSectionMap t i s) := by
      rw [h]
      exact ⟨fun hx => ⟨u.2, hx⟩, And.right⟩
    _ ↔ _ := by
      dsimp only [s]
      rw [curveChartSectionMap_coordinate, chart_section_prime, specializedCoordinateChartEquiv_map]
      change (_ ∉ (e.hom u).asIdeal) ↔ _
      rw [hz]

theorem seedCoordinateSectionsEquiv_fraction (n : ℕ) (P : CycleQ2SeedTrace.WeightedPoly)
    (hP : P.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight n) :
    seedCoordinateSectionsEquiv i (homogeneousFraction seed i.succ n P hP) =
      polynomialSection i (Patch i) le_rfl P := by
  change (Proj.basicOpenIsoAway (CycleQ2CartierSurfaceGrading.surfaceGrade 57 1)
      (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 (X i.succ.castSucc))
      (CycleQ2GeometricSurfaceDehomogenizedCharts.coordinate_mem_grade 57 1 i.succ)
      (by decide)).hom (literalCartierLocalizationEquiv (X i.succ.castSucc)
        (homogeneousFraction seed i.succ n P hP)) = _
  rw [literalCartierLocalizationEquiv_fraction]
  have h := CycleQ2SurfaceCoordinateSections.coordinatePolynomialSection_fraction 57 1 i.succ
    (Patch i) le_rfl n P hP
  simpa only [homOfLE_refl, op_id, Surface.presheaf.map_id, ConcreteCategory.id_apply,
    polynomialSection, chartSectionMap, affinePolynomial,
    CycleQ2SurfaceCoordinateSections.coordinatePolynomialSection] using h.symm

theorem mem_polynomial_basicOpen_iff (z : PrimeSpectrum (AffineCurveChart seed t i.succ))
    (n : ℕ) (P : CycleQ2SeedTrace.WeightedPoly)
    (hP : P.IsWeightedHomogeneous CycleQ2CartierSurfaceGrading.weight n) :
    curveToSurface t (seedChartToCurve t i.succ z) ∈
        Surface.basicOpen (polynomialSection i (Patch i) le_rfl P) ↔
      curvePolynomialMap t i.succ seed (dehomogenize i.succ P) ∉ z.asIdeal := by
  rw [← seedCoordinateSectionsEquiv_fraction i n P hP, mem_basicOpen_iff,
    familyCoordinateChartEquiv_homogeneousFraction]
  rfl

theorem mem_pivotOpen_iff (z : PrimeSpectrum (AffineCurveChart seed t i.succ))
    (p : CycleQ2SegreCech.Chart) :
    curveToSurface t (seedChartToCurve t i.succ z) ∈ pivotOpen i p ↔
      Ideal.Quotient.mk (affineSectionIdeal seed t i.succ) (seedPivot i.succ p) ∉ z.asIdeal := by
  rw [pivotOpen, sectionMatrix_entry, ← CycleQ2SeedConeSection.pointMatrixPolynomial_seed]
  rw [mem_polynomial_basicOpen_iff t i z 14 _ (pointMatrixPolynomial_homogeneous seed p.1 p.2)]
  rw [seedPivot, affineMatrixEntry_polynomial]
  rfl

#print axioms exists_literalChart_prime
#print axioms mem_basicOpen_iff
#print axioms mem_polynomial_basicOpen_iff
#print axioms mem_pivotOpen_iff

end CycleQ2LiteralResidueRowPoint

end
