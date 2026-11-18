import Proposal.GeometricLiteralCoordinateTwistPrimitives
import Proposal.GeometricLiteralOrbitNegativeSections
import Proposal.GeometricGradedIdealContraction
import Proposal.GeometricSeedSectionDivisorFrames

/-!
# The orbit ideal in the coordinate fractions of the moving curve

The three degree-ten equations differ from the chart orbit generators by the
same invertible coordinate power. Extension and contraction through the genuine
degree-zero localization therefore recover the image of the original
twisted ideal on every nonempty coordinate intersection.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTwistedOrbitMembership

open CategoryTheory AlgebraicGeometry CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedSectionSheaf CycleQ2SeedSectionSheafSections
  CycleQ2SeedSectionSheafIdealOverlap CycleQ2SeedSectionSheafLocal
  CycleQ2SeedSectionDivisorFrames CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricCartierNormalLift CycleQ2CartierSurfaceGrading
  CycleQ2ProjectiveCoordinateCohomology CycleQ2ProjectiveCoordinateH2
  CycleQ2SurfaceSectionCoefficients CycleQ2LiteralCoordinateTwistPrimitives
  CycleQ2LiteralOrbitNegativeSections

abbrev patchIdeal (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I) : Ideal Γ(Surface,U I) :=
  Ideal.span (Set.range (sectionLeft i (U I) (intersection_le_chart 57 1 i hi)))

theorem source_range (I : Finset (Fin 3)) (i : Fin 3) (hi : i ∈ I) :
    LinearMap.range (sourceCoordinate i (U I) (intersection_le_chart 57 1 i hi)) = patchIdeal I i hi := by
  let V := U I
  let hV := intersection_le_chart 57 1 i hi
  rw [patchIdeal, ← idealCoordinate_range_span]
  ext x
  constructor
  · rintro ⟨a,rfl⟩
    exact ⟨(chartProjection i).app V a,rfl⟩
  · rintro ⟨a,rfl⟩
    obtain ⟨b,rfl⟩ := chartProjection_app_surjective i V hV a
    exact ⟨b,rfl⟩

private def numerator (I : Finset (Fin 3)) (a : Fin 3) : cone I :=
  algebraMap (SurfaceRing 57 1) (cone I)
    (surfaceQuotient 57 1 (CycleQ2SeedFactorHomogeneous.polynomialLeft (57 : ℂ) a))

private theorem sectionLeft_coefficient (I : Finset (Fin 3)) (hI : I.Nonempty)
    (i : Fin 3) (hi : i ∈ I) (a : Fin 3) :
    sectionCoefficient 57 1 I hI (sectionLeft i (U I) (intersection_le_chart 57 1 i hi) a) *
      (↑(xUnit I i hi ^ 10) : cone I) = numerator I a := by
  rw [sectionLeft_entry]
  change sectionCoefficient 57 1 I hI (CycleQ2SurfaceCoordinateSections.coordinatePolynomialSection
    57 1 (chartIndex i) (U I) _ _) * (↑(xUnit I i hi ^ 10) : cone I) = _
  have h := sectionCoefficient_homogeneous 57 1 hI i hi 10
    (CycleQ2SeedFactorHomogeneous.polynomialLeft (57 : ℂ) a)
    (CycleQ2GeometricIncidenceProj.homogeneous_of_character
      (CycleQ2SeedFactorHomogeneous.polynomialLeft_homogeneous (57 : ℂ) a))
  simpa only [xUnit, Units.val_pow_eq_pow_val, IsUnit.unit_spec, map_pow, numerator] using h

/-- Extension to the cone sections reproduces the native orbit ideal. -/
theorem patchIdeal_map (I : Finset (Fin 3)) (hI : I.Nonempty) (i : Fin 3) (hi : i ∈ I) :
    (patchIdeal I i hi).map (sectionCoefficient 57 1 I hI) = chartOrbitIdeal I := by
  rw [patchIdeal, Ideal.map_span, ← Set.range_comp, chartOrbitIdeal_eq_span I hI]
  change Ideal.span (Set.range _) = Ideal.span (Set.range (numerator I))
  apply le_antisymm <;> apply Ideal.span_le.mpr <;> rintro _ ⟨a,rfl⟩
  · let J := Ideal.span (Set.range (numerator I))
    let u := xUnit I i hi ^ 10
    have h : numerator I a ∈ J := Ideal.subset_span (Set.mem_range_self a)
    have hm := J.mul_mem_right (↑u⁻¹ : cone I) h
    rw [← sectionLeft_coefficient I hI i hi a] at hm
    change sectionCoefficient 57 1 I hI (sectionLeft i (U I) (intersection_le_chart 57 1 i hi) a) ∈ J
    simpa only [u, mul_assoc, Units.mul_inv, mul_one] using hm
  · rw [← sectionLeft_coefficient I hI i hi a]
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span (Set.mem_range_self a))

/-- Contraction through degree zero returns exactly the projective chart ideal. -/
theorem sectionCoefficient_comap (I : Finset (Fin 3)) (hI : I.Nonempty)
    (i : Fin 3) (hi : i ∈ I) :
    (chartOrbitIdeal I).comap (sectionCoefficient 57 1 I hI) = patchIdeal I i hi := by
  let e := (coordinateSections 57 1 I hI).symm
  let φ := algebraMap (HomogeneousCoordinateLocal 57 1 I) (cone I)
  rw [← patchIdeal_map I hI i hi]
  change ((patchIdeal I i hi).map (φ.comp e.toRingHom)).comap (φ.comp e.toRingHom) = _
  rw [← Ideal.map_map, ← Ideal.comap_comap,
    CycleQ2GradedIdealContraction.ideal_map_comap_val (surfaceGrade 57 1) (coordinateProduct_mem_grade 57 1 I)]
  exact Ideal.comap_map_of_bijective e.toRingHom e.bijective

theorem encode_mem_iff (k : ℤ) (I : Finset (Fin 3)) (hI : I.Nonempty)
    (i : Fin 3) (hi : i ∈ I) (a : Γ(Surface,U I)) :
    encode k I hI i hi a ∈ chartOrbitIdeal I ↔
      a ∈ LinearMap.range (sourceCoordinate i (U I) (intersection_le_chart 57 1 i hi)) := by
  rw [source_range I i hi, ← sectionCoefficient_comap I hI i hi]
  change (↑(xUnit I i hi ^ k) : cone I) * sectionCoefficient 57 1 I hI a ∈ chartOrbitIdeal I ↔
    sectionCoefficient 57 1 I hI a ∈ chartOrbitIdeal I
  exact Ideal.unit_mul_mem_iff_mem _ (xUnit I i hi ^ k).isUnit

end CycleQ2LiteralTwistedOrbitMembership
end

#print axioms CycleQ2LiteralTwistedOrbitMembership.encode_mem_iff
