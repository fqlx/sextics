import Proposal.GeometricLiteralIntersectionEpsilonTransport
import Proposal.GeometricLiteralNativeHomogeneousFractions

/-!
# The marked universal deformation on the original refined cone intersections

The marked family and the literal square-zero deformation use the same cubic,
sextic and perturbation. Localizing the identity on polynomial coordinates
and epsilon compares their rings on every common refinement.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 2000000
set_option maxRecDepth 4400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2IncidenceMarkedProjectorCharts

open MvPolynomial CycleQ2SeedTrace CycleQ2SeedQuotientFiniteFree CycleQ2SeedCechThreeOpen
  CycleQ2SeedCechLocalization CycleQ2NormalConnecting CycleQ2GeometricSeedNormalIdeals
  CycleQ2GeometricSeedNormalizedCoordinates CycleQ2GeometricKernelLocalization
  CycleQ2GeometricUniversalSurfaceFirstOrder CycleQ2LiteralCartierTransitionBinding
  CycleQ2LiteralCartierOverlapSplittings CycleQ2LiteralGradedDeformation
  CycleQ2LiteralGradedDeformationEquiv CycleQ2LiteralGradedReduction
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionProjection
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralNativeHomogeneousFractions
  CycleQ2LiteralIntersectionEpsilonTransport

attribute [local instance] CycleQ2LiteralCartierTransitionBinding.cubicSelfModule
  CycleQ2LiteralCartierTransitionBinding.cubicOppositeModule
  CycleQ2LiteralCartierTransitionBinding.cubicCentralScalar
  CycleQ2LiteralCartierTransitionBinding.cubicSmulCommClass
  CycleQ2GeometricSurfaceFirstOrder.reducedAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralCartierSplittings.complexReductionTower
  CycleQ2LiteralCartierOverlapSplittings.baseReductionAlgebra

private abbrev den (I : Finset (Fin 3)) : ThickBase :=
  CycleQ2GeometricSurfaceFirstOrder.deformationCoordinate equation perturbation (coordinateClass ℂ (cubicCoefficients 57) I)

private abbrev thickBaseMap := CycleQ2LiteralConeIntersectionTransport.thickBaseMap
private abbrev closedBaseMap := CycleQ2LiteralConeIntersectionTransport.closedBaseMap
private abbrev baseReduction := CycleQ2GeometricSurfaceFirstOrder.reduction equation perturbation

abbrev MarkedThick (I : Finset (Fin 3)) := Localization.Away (den I)
abbrev baseToMarked (I : Finset (Fin 3)) : ThickBase →+* MarkedThick I :=
  @Algebra.algebraMap ThickBase (MarkedThick I)
    (inferInstance : CommSemiring ThickBase) (inferInstance : Semiring (MarkedThick I)) inferInstance

abbrev MarkedClosed := NormalizedLocal 57
abbrev markedReduction (I : Finset (Fin 3)) : MarkedThick I →+* MarkedClosed I :=
  localSurfaceReduction ℂ (cubicCoefficients 57) (sexticCoefficients 57) derivativeA I
abbrev markedCoefficients (I : Finset (Fin 3)) : CycleQ2GeometricProjectorDefect.Coefficients (markedReduction I) :=
  localSurfaceCoefficients ℂ (cubicCoefficients 57) (sexticCoefficients 57) derivativeA I
theorem markedReduction_surjective (I : Finset (Fin 3)) : Function.Surjective (markedReduction I) :=
  localSurfaceReduction_surjective ℂ (cubicCoefficients 57) (sexticCoefficients 57) derivativeA I

private abbrev markedClosedEquiv (I : Finset (Fin 3)) :
    Localization.Away (baseReduction (den I)) ≃+* MarkedClosed I :=
  localClosedSurfaceEquiv ℂ (cubicCoefficients 57) (sexticCoefficients 57) derivativeA I

def Admits (t : Finset Vertex) (I : Finset (Fin 3)) : Prop :=
  ∀ i ∈ I, ∃ a, (a,i) ∈ t

private theorem thickBaseMap_variable (t : Finset Vertex) (i : Fin 3) :
    thickBaseMap t (originalPolynomial (X (remainingIndex i))) =
      algebraMap GradedDeformation (ThickCone t) (CycleQ2LiteralProjectiveDeformation.coordinateElement i) := by
  change algebraMap GradedDeformation (ThickCone t) (fromOriginal (originalPolynomial _)) = _
  rw [fromOriginal_polynomial]
  simp only [polynomialInGraded, AlgHom.comp_apply, includePolynomial, rename_X, CycleQ2LiteralProjectiveDeformation.coordinateElement, coordinate]

private theorem denominator_unit (t : Finset Vertex) (I : Finset (Fin 3)) (h : Admits t I) :
    IsUnit (thickBaseMap t (den I)) := by
  change IsUnit (thickBaseMap t (originalPolynomial (remainingInclusion ℂ (baseProduct ℂ I))))
  simp only [baseProduct, map_prod, remainingInclusion, rename_X]
  apply IsUnit.prod_iff.mpr
  intro i hi
  obtain ⟨a,ha⟩ := h i hi
  rw [thickBaseMap_variable]
  exact coordinateValue_isUnit t (a,i) ha

/-- Coordinate localization on the marked fibre maps to the fixed thick cone intersection. -/
def thickMap (t : Finset Vertex) (I : Finset (Fin 3)) (h : Admits t I) :
    MarkedThick I →+* ThickCone t :=
  IsLocalization.Away.lift (den I) (g := (thickBaseMap t).toRingHom) (denominator_unit t I h)

theorem thickMap_base (t : Finset Vertex) (I : Finset (Fin 3)) (h : Admits t I) (z : ThickBase) :
    thickMap t I h (baseToMarked I z) = thickBaseMap t z :=
  IsLocalization.Away.lift_eq (S := MarkedThick I) (den I) (g := (thickBaseMap t).toRingHom) (denominator_unit t I h) z

private theorem reduction_base (t : Finset Vertex) (z : ThickBase) :
    ordinaryReduction t (thickBaseMap t z) = closedBaseMap t (baseReduction z) := by
  change ordinaryReduction t (algebraMap GradedDeformation (ThickCone t) (fromOriginal z)) =
    algebraMap (SurfaceRing 57 1) (ClosedCone t) (closedAlgEquiv (baseReduction z))
  rw [CycleQ2LiteralProjectiveIntersectionRestrictions.ordinaryReduction_base,
    reduction_eq_original, toOriginal_fromOriginal]

private def rawClosedMap (t : Finset Vertex) (I : Finset (Fin 3)) (h : Admits t I) :
    Localization.Away (baseReduction (den I)) →+* ClosedCone t :=
  IsLocalization.Away.lift (baseReduction (den I)) (g := (closedBaseMap t).toRingHom)
    ((reduction_base t (den I)) ▸ (denominator_unit t I h).map (ordinaryReduction t))

/-- The closed-fibre map uses the original normalized surface at the marked point. -/
def closedMap (t : Finset Vertex) (I : Finset (Fin 3)) (h : Admits t I) :
    MarkedClosed I →+* ClosedCone t :=
  (rawClosedMap t I h).comp (markedClosedEquiv I).symm.toRingHom

theorem reduction_thickMap (t : Finset Vertex) (I : Finset (Fin 3)) (h : Admits t I)
    (z : MarkedThick I) :
    ordinaryReduction t (thickMap t I h z) = closedMap t I h (markedReduction I z) := by
  change _ = rawClosedMap t I h ((markedClosedEquiv I).symm ((markedClosedEquiv I) _))
  rw [RingEquiv.symm_apply_apply]
  have he : (ordinaryReduction t).comp (thickMap t I h) =
      (rawClosedMap t I h).comp (localReduction ThickBase ClosedBase (den I)) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (den I))
    apply RingHom.ext
    intro b
    have hraw (y : ClosedBase) :
        rawClosedMap t I h (@Algebra.algebraMap ClosedBase (Localization.Away (baseReduction (den I)))
          (inferInstance : CommSemiring ClosedBase) (inferInstance : Semiring (Localization.Away (baseReduction (den I)))) inferInstance y) = closedBaseMap t y :=
      IsLocalization.Away.lift_eq (g := (closedBaseMap t).toRingHom) (baseReduction (den I))
        ((reduction_base t (den I)) ▸ (denominator_unit t I h).map (ordinaryReduction t)) y
    exact (congrArg (ordinaryReduction t) (thickMap_base t I h b)).trans
      ((reduction_base t b).trans ((hraw (baseReduction b)).symm.trans
        (congrArg (rawClosedMap t I h) (localReduction_base ThickBase ClosedBase (den I) b).symm)))
  exact RingHom.congr_fun he z

theorem thickMap_epsilon (t : Finset Vertex) (I : Finset (Fin 3)) (h : Admits t I) :
    thickMap t I h (baseToMarked I originalEpsilon) = ordinaryEpsilon t := by
  rw [thickMap_base]
  exact congrArg (algebraMap GradedDeformation (ThickCone t)) fromOriginal_epsilon

/-- The actual square-zero kernel on the refined ambient intersection,
in the coefficient interface used by the relative projector cocycle. -/
def coneCoefficients (t : Finset Vertex) : CycleQ2GeometricProjectorDefect.Coefficients (ordinaryReduction t) where
  epsilon := (ordinaryCoefficientLinear t).toAddMonoidHom
  injective := ordinaryCoefficient_injective t
  reduction_epsilon := ordinaryCoefficient_reduction t
  exact_kernel z hz := by
    obtain ⟨x,hx⟩ := (ordinaryKernelEquiv t).surjective ⟨z,hz⟩
    exact ⟨x, congrArg Subtype.val hx⟩
  mul_epsilon z x := by
    obtain ⟨u,rfl⟩ := CycleQ2LiteralProjectiveIntersectionSplittings.ordinaryReduction_surjective t x
    change z * ordinaryCoefficient t (ordinaryReduction t u) =
      ordinaryCoefficient t (ordinaryReduction t z * ordinaryReduction t u)
    rw [← map_mul, ordinaryCoefficient_of_reduction, ordinaryCoefficient_of_reduction]
    ring
  epsilon_mul x z := by
    obtain ⟨u,rfl⟩ := CycleQ2LiteralProjectiveIntersectionSplittings.ordinaryReduction_surjective t x
    change ordinaryCoefficient t (ordinaryReduction t u) * z =
      ordinaryCoefficient t (ordinaryReduction t u * ordinaryReduction t z)
    rw [← map_mul, ordinaryCoefficient_of_reduction, ordinaryCoefficient_of_reduction]
    ring

theorem markedEpsilon_one (I : Finset (Fin 3)) :
    (markedCoefficients I).epsilon 1 = baseToMarked I originalEpsilon := by
  have h := localSurfaceCoefficients_epsilon_base ℂ (cubicCoefficients 57) (sexticCoefficients 57)
    derivativeA I (1 : NormalizedSurface 57)
  rw [map_one] at h
  have he := surfaceEpsilon_mk ℂ (cubicCoefficients 57) (sexticCoefficients 57) derivativeA
    (1 : WeightedPoly)
  simp only [map_one] at he
  exact h.trans (congrArg (baseToMarked I) he)

/-- The entire square-zero inclusion commutes with the marked specialization. -/
theorem thickMap_coefficients (t : Finset Vertex) (I : Finset (Fin 3)) (h : Admits t I)
    (x : MarkedClosed I) :
    thickMap t I h ((markedCoefficients I).epsilon x) = ordinaryCoefficient t (closedMap t I h x) := by
  obtain ⟨z,rfl⟩ := markedReduction_surjective I x
  have he := ((markedCoefficients I).epsilon_mul 1 z).symm
  rw [one_mul] at he
  change thickMap t I h ((markedCoefficients I).epsilon (markedReduction I z)) =
    ordinaryCoefficient t (closedMap t I h (markedReduction I z))
  rw [he, map_mul, markedEpsilon_one, thickMap_epsilon]
  exact (ordinaryCoefficient_of_reduction t (thickMap t I h z)).symm.trans
    (congrArg (ordinaryCoefficient t) (reduction_thickMap t I h z))

/-- Extraction of a kernel coefficient agrees with the native epsilon after transport. -/
theorem closedMap_coefficient (t : Finset Vertex) (I : Finset (Fin 3)) (h : Admits t I)
    (z : MarkedThick I) (hz : markedReduction I z = 0) :
    ordinaryCoefficient t (closedMap t I h ((markedCoefficients I).coefficient z hz)) = thickMap t I h z := by
  rw [← thickMap_coefficients, CycleQ2GeometricProjectorDefect.Coefficients.epsilon_coefficient]

theorem thickMap_polynomial (t : Finset Vertex) (I : Finset (Fin 3)) (h : Admits t I)
    (p : WeightedPoly) :
    thickMap t I h (baseToMarked I (originalPolynomial p)) =
      algebraMap GradedDeformation (ThickCone t) (polynomialInGraded p) := by
  rw [thickMap_base]
  exact congrArg (algebraMap GradedDeformation (ThickCone t)) (fromOriginal_polynomial p)

theorem closedMap_polynomial (t : Finset Vertex) (I : Finset (Fin 3)) (h : Admits t I)
    (p : WeightedPoly) :
    closedMap t I h (algebraMap (NormalizedSurface 57) (MarkedClosed I)
      (Ideal.Quotient.mk (CycleQ2UniversalSurface.surfaceIdeal ℂ (cubicCoefficients 57) (sexticCoefficients 57)) p)) =
      algebraMap (SurfaceRing 57 1) (ClosedCone t) (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 p) := by
  let q := baseToMarked I (originalPolynomial p)
  have hr : markedReduction I q = algebraMap (NormalizedSurface 57) (MarkedClosed I)
      (Ideal.Quotient.mk (CycleQ2UniversalSurface.surfaceIdeal ℂ (cubicCoefficients 57) (sexticCoefficients 57)) p) := by
    change markedClosedEquiv I (localReduction ThickBase ClosedBase (den I) (baseToMarked I (originalPolynomial p))) = _
    exact (congrArg (markedClosedEquiv I) (localReduction_base ThickBase ClosedBase (den I) (originalPolynomial p))).trans
      (localClosedSurfaceEquiv_base ℂ (cubicCoefficients 57) (sexticCoefficients 57) derivativeA I (baseReduction (originalPolynomial p)))
  rw [← hr, ← reduction_thickMap]
  change ordinaryReduction t (thickMap t I h (baseToMarked I (originalPolynomial p))) = _
  rw [thickMap_polynomial, CycleQ2LiteralProjectiveIntersectionRestrictions.ordinaryReduction_base, reduction_polynomial]

theorem admits_subset {t : Finset Vertex} {I J : Finset (Fin 3)} (hIJ : I ⊆ J)
    (h : Admits t J) : Admits t I := fun i hi => h i (hIJ hi)

theorem admits_mono {s t : Finset Vertex} (hst : s ⊆ t) {I : Finset (Fin 3)}
    (h : Admits s I) : Admits t I := by
  intro i hi
  obtain ⟨a,ha⟩ := h i hi
  exact ⟨a,hst ha⟩

abbrev markedRestriction {I J : Finset (Fin 3)} (hIJ : I ⊆ J) : MarkedThick I →+* MarkedThick J :=
  localSurfaceRestriction ℂ (cubicCoefficients 57) (sexticCoefficients 57) derivativeA hIJ

theorem thickMap_restrict_source (t : Finset Vertex) {I J : Finset (Fin 3)} (hIJ : I ⊆ J)
    (h : Admits t J) (x : MarkedThick I) :
    thickMap t J h (markedRestriction hIJ x) = thickMap t I (admits_subset hIJ h) x := by
  have he : (thickMap t J h).comp (markedRestriction hIJ) = thickMap t I (admits_subset hIJ h) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (den I))
    apply RingHom.ext
    intro z
    let hd := deformationCoordinate_dvd ℂ (cubicCoefficients 57) (sexticCoefficients 57) derivativeA hIJ
    exact (congrArg (thickMap t J h) (CycleQ2GeometricKernelLocalization.thickRestriction_base ThickBase hd z)).trans
      ((thickMap_base t J h z).trans (thickMap_base t I (admits_subset hIJ h) z).symm)
  exact RingHom.congr_fun he x

theorem thickMap_restrict_target {s t : Finset Vertex} (hst : s ⊆ t)
    (I : Finset (Fin 3)) (h : Admits s I) (x : MarkedThick I) :
    thickConeRestriction hst (thickMap s I h x) = thickMap t I (admits_mono hst h) x := by
  have he : (thickConeRestriction hst).toRingHom.comp (thickMap s I h) =
      thickMap t I (admits_mono hst h) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (den I))
    apply RingHom.ext
    intro z
    exact (congrArg (thickConeRestriction hst) (thickMap_base s I h z)).trans
      ((thickConeRestriction_base hst (fromOriginal z)).trans (thickMap_base t I (admits_mono hst h) z).symm)
  exact RingHom.congr_fun he x

theorem closedMap_restrict_source (t : Finset Vertex) {I J : Finset (Fin 3)} (hIJ : I ⊆ J)
    (h : Admits t J) (x : MarkedClosed I) :
    closedMap t J h (CycleQ2UniversalSurfaceRestrictions.restriction ℂ
      (cubicCoefficients 57) (sexticCoefficients 57) hIJ x) = closedMap t I (admits_subset hIJ h) x := by
  obtain ⟨z,rfl⟩ := markedReduction_surjective I x
  have hz : markedReduction J (markedRestriction hIJ z) = CycleQ2UniversalSurfaceRestrictions.restriction ℂ
      (cubicCoefficients 57) (sexticCoefficients 57) hIJ (markedReduction I z) :=
    localSurfaceReduction_restriction ℂ (cubicCoefficients 57) (sexticCoefficients 57) derivativeA hIJ z
  exact (congrArg (closedMap t J h) hz.symm).trans
    ((reduction_thickMap t J h (markedRestriction hIJ z)).symm.trans
      ((congrArg (ordinaryReduction t) (thickMap_restrict_source t hIJ h z)).trans
        (reduction_thickMap t I (admits_subset hIJ h) z)))

theorem closedMap_restrict_target {s t : Finset Vertex} (hst : s ⊆ t)
    (I : Finset (Fin 3)) (h : Admits s I) (x : MarkedClosed I) :
    closedConeRestriction hst (closedMap s I h x) = closedMap t I (admits_mono hst h) x := by
  obtain ⟨z,rfl⟩ := markedReduction_surjective I x
  exact (congrArg (closedConeRestriction hst) (reduction_thickMap s I h z).symm).trans
    ((ordinaryReduction_restrict hst (thickMap s I h z)).symm.trans
      ((congrArg (ordinaryReduction t) (thickMap_restrict_target hst I h z)).trans
        (reduction_thickMap t I (admits_mono hst h) z)))

section FurtherLocalization

attribute [local instance] CycleQ2LiteralIntersectionEpsilonTransport.ordinaryReductionAlgebra

abbrev RefinedThick (t : Finset Vertex) (q : ThickCone t) := Localization.Away q
abbrev RefinedClosed (t : Finset Vertex) (q : ThickCone t) := Localization.Away (ordinaryReduction t q)

def refinedReduction (t : Finset Vertex) (q : ThickCone t) :
    RefinedThick t q →+* RefinedClosed t q := localReduction (ThickCone t) (ClosedCone t) q

def refinedCoefficients (t : Finset Vertex) (q : ThickCone t) :
    CycleQ2GeometricProjectorDefect.Coefficients (refinedReduction t q) :=
  localizedCoefficients (ThickCone t) (ClosedCone t) (ordinaryKernelEquiv t) q

def refinedThickMap (t : Finset Vertex) (q : ThickCone t) (I : Finset (Fin 3)) (h : Admits t I) :
    MarkedThick I →+* RefinedThick t q := (algebraMap _ _).comp (thickMap t I h)

def refinedClosedMap (t : Finset Vertex) (q : ThickCone t) (I : Finset (Fin 3)) (h : Admits t I) :
    MarkedClosed I →+* RefinedClosed t q := (algebraMap _ _).comp (closedMap t I h)

theorem refinedReduction_base (t : Finset Vertex) (q z : ThickCone t) :
    refinedReduction t q (algebraMap _ (RefinedThick t q) z) =
      algebraMap _ (RefinedClosed t q) (ordinaryReduction t z) :=
  localReduction_base (ThickCone t) (ClosedCone t) q z

theorem refinedReduction_thickMap (t : Finset Vertex) (q : ThickCone t) (I : Finset (Fin 3))
    (h : Admits t I) (z : MarkedThick I) :
    refinedReduction t q (refinedThickMap t q I h z) = refinedClosedMap t q I h (markedReduction I z) := by
  exact (refinedReduction_base t q (thickMap t I h z)).trans (congrArg
    (algebraMap (ClosedCone t) (RefinedClosed t q)) (reduction_thickMap t I h z))

theorem refinedCoefficients_base (t : Finset Vertex) (q : ThickCone t) (x : ClosedCone t) :
    (refinedCoefficients t q).epsilon (algebraMap _ (RefinedClosed t q) x) =
      algebraMap _ (RefinedThick t q) (ordinaryCoefficient t x) :=
  localizedCoefficients_epsilon_base (ThickCone t) (ClosedCone t) (ordinaryKernelEquiv t) q x

/-- Coefficient compatibility persists after inverting a further pivot denominator. -/
theorem refinedThickMap_coefficients (t : Finset Vertex) (q : ThickCone t) (I : Finset (Fin 3))
    (h : Admits t I) (x : MarkedClosed I) :
    refinedThickMap t q I h ((markedCoefficients I).epsilon x) =
      (refinedCoefficients t q).epsilon (refinedClosedMap t q I h x) := by
  exact (congrArg (algebraMap (ThickCone t) (RefinedThick t q))
    (thickMap_coefficients t I h x)).trans (refinedCoefficients_base t q (closedMap t I h x)).symm

/-- The homogeneous lift of any polynomial matrix entry in the original coordinates. -/
def polynomialPivot (t : Finset Vertex) (p : WeightedPoly) : ThickCone t :=
  algebraMap GradedDeformation (ThickCone t) (polynomialInGraded p)

theorem polynomialPivot_reduction (t : Finset Vertex) (p : WeightedPoly) :
    ordinaryReduction t (polynomialPivot t p) =
      algebraMap (SurfaceRing 57 1) (ClosedCone t) (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 p) := by
  rw [polynomialPivot, CycleQ2LiteralProjectiveIntersectionRestrictions.ordinaryReduction_base, reduction_polynomial]

theorem polynomialPivot_homogeneous {p : WeightedPoly} {d : ℕ}
    (hp : p.IsWeightedHomogeneous CycleQ2GeometricCoordinateWeight.weight d) :
    polynomialInGraded p ∈ deformationGrade d :=
  quotientMap_mem_grade (includePolynomial_homogeneous hp)

variable {ι : Type} (t : Finset Vertex) (P : ι → WeightedPoly) (S : Finset ι)

/-- A further cone open where every selected pivot is invertible. -/
def pivotProduct : ThickCone t := ∏ i ∈ S, polynomialPivot t (P i)

def gradedPivotProduct : GradedDeformation := ∏ i ∈ S, polynomialInGraded (P i)

theorem pivotProduct_eq :
    pivotProduct t P S = algebraMap GradedDeformation (ThickCone t) (gradedPivotProduct P S) := by
  simp only [pivotProduct, polynomialPivot, gradedPivotProduct, map_prod]

theorem gradedPivotProduct_homogeneous (d : ι → ℕ)
    (h : ∀ i ∈ S, (P i).IsWeightedHomogeneous CycleQ2GeometricCoordinateWeight.weight (d i)) :
    gradedPivotProduct P S ∈ deformationGrade (∑ i ∈ S, d i) :=
  SetLike.prod_mem_graded deformationGrade d _ (fun i hi => polynomialPivot_homogeneous (h i hi))

theorem pivotProduct_reduction :
    ordinaryReduction t (pivotProduct t P S) =
      ∏ i ∈ S, algebraMap (SurfaceRing 57 1) (ClosedCone t) (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 (P i)) := by
  simp only [pivotProduct, map_prod, polynomialPivot_reduction]

theorem polynomialPivot_isUnit (i : ι) (hi : i ∈ S) :
    IsUnit (algebraMap _ (RefinedThick t (pivotProduct t P S)) (polynomialPivot t (P i))) :=
  IsLocalization.Away.isUnit_of_dvd (pivotProduct t P S) (Finset.dvd_prod_of_mem _ hi)

theorem closedPolynomialPivot_isUnit (i : ι) (hi : i ∈ S) :
    IsUnit (algebraMap _ (RefinedClosed t (pivotProduct t P S))
      (algebraMap (SurfaceRing 57 1) (ClosedCone t) (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1 (P i)))) := by
  have h := (polynomialPivot_isUnit t P S i hi).map (refinedReduction t (pivotProduct t P S))
  rw [refinedReduction_base, polynomialPivot_reduction] at h
  exact h

end FurtherLocalization

end CycleQ2IncidenceMarkedProjectorCharts
end

#print axioms CycleQ2IncidenceMarkedProjectorCharts.reduction_thickMap
#print axioms CycleQ2IncidenceMarkedProjectorCharts.thickMap_epsilon

#print axioms CycleQ2IncidenceMarkedProjectorCharts.closedMap_coefficient
#print axioms CycleQ2IncidenceMarkedProjectorCharts.closedMap_restrict_target

#print axioms CycleQ2IncidenceMarkedProjectorCharts.refinedThickMap_coefficients
#print axioms CycleQ2IncidenceMarkedProjectorCharts.closedPolynomialPivot_isUnit
