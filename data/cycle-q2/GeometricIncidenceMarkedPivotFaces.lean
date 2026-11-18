import Proposal.GeometricIncidenceMarkedProjectorCharts
import Proposal.GeometricLiteralMovingDivisorChern

/-!
# Restriction maps on the retained moving-divisor pivot faces

For a finite set of pivot vertices, invert the product of the genuine
polynomial matrix entries on its native cone intersection. Increasing the
set restricts both the square-zero deformation ring and its reduction.
These restriction maps preserve the identified epsilon kernel.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 2400
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceMarkedPivotFaces

open CycleQ2IncidenceEquations CycleQ2LiteralMovingDivisorChern CycleQ2SeedTrace
  CycleQ2LiteralGradedDeformation CycleQ2LiteralGradedReduction CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralProjectiveIntersectionKernel
  CycleQ2LiteralIntersectionEpsilonTransport CycleQ2IncidenceMarkedProjectorCharts
  CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2GeometricKernelLocalization

attribute [local instance] ordinaryReductionAlgebra

abbrev Face := Finset VertexIndex
abbrev vertices (S : Face) : Finset Vertex := S.image Prod.fst
def seedPivot (a : VertexIndex) : WeightedPoly := rawSeedMatrix (57 : ℂ) a.2.1 a.2.2
abbrev pivotDen (S : Face) := pivotProduct (vertices S) seedPivot S
abbrev faceThick (S : Face) := RefinedThick (vertices S) (pivotDen S)
abbrev faceClosed (S : Face) := RefinedClosed (vertices S) (pivotDen S)
abbrev faceReduction (S : Face) := refinedReduction (vertices S) (pivotDen S)
abbrev faceCoefficients (S : Face) := refinedCoefficients (vertices S) (pivotDen S)
abbrev vertices_mono {S T : Face} (h : S ⊆ T) : vertices S ⊆ vertices T := Finset.image_subset_image h

abbrev toThick (S : Face) : ThickCone (vertices S) →+* faceThick S := algebraMap _ _
abbrev toClosed (S : Face) : ClosedCone (vertices S) →+* faceClosed S := algebraMap _ _

private theorem thick_unit {S T : Face} (h : S ⊆ T) :
    IsUnit (toThick T (thickConeRestriction (vertices_mono h) (pivotDen S))) := by
  simp only [pivotDen, pivotProduct, map_prod, polynomialPivot, thickConeRestriction_base]
  apply IsUnit.prod_iff.mpr
  intro i hi
  exact polynomialPivot_isUnit (vertices T) seedPivot T i (h hi)

private theorem closed_unit {S T : Face} (h : S ⊆ T) :
    IsUnit (toClosed T (closedConeRestriction (vertices_mono h) (ordinaryReduction (vertices S) (pivotDen S)))) := by
  rw [pivotProduct_reduction]
  simp only [map_prod, closedConeRestriction_base]
  apply IsUnit.prod_iff.mpr
  intro i hi
  exact closedPolynomialPivot_isUnit (vertices T) seedPivot T i (h hi)

def faceThickRestrict {S T : Face} (h : S ⊆ T) : faceThick S →+* faceThick T :=
  IsLocalization.Away.lift (pivotDen S) (g := (toThick T).comp (thickConeRestriction (vertices_mono h)).toRingHom)
    (thick_unit h)

def faceClosedRestrict {S T : Face} (h : S ⊆ T) : faceClosed S →+* faceClosed T :=
  IsLocalization.Away.lift (ordinaryReduction (vertices S) (pivotDen S))
    (g := (toClosed T).comp (closedConeRestriction (vertices_mono h)).toRingHom) (closed_unit h)

theorem faceThickRestrict_base {S T : Face} (h : S ⊆ T) (x : ThickCone (vertices S)) :
    faceThickRestrict h (toThick S x) = toThick T (thickConeRestriction (vertices_mono h) x) :=
  IsLocalization.Away.lift_eq _ _ x

theorem faceClosedRestrict_base {S T : Face} (h : S ⊆ T) (x : ClosedCone (vertices S)) :
    faceClosedRestrict h (toClosed S x) = toClosed T (closedConeRestriction (vertices_mono h) x) :=
  IsLocalization.Away.lift_eq _ _ x

theorem faceThickRestrict_comp {S T U : Face} (h : S ⊆ T) (k : T ⊆ U) (x : faceThick S) :
    faceThickRestrict k (faceThickRestrict h x) = faceThickRestrict (h.trans k) x := by
  have he : (faceThickRestrict k).comp (faceThickRestrict h) = faceThickRestrict (h.trans k) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (pivotDen S))
    apply RingHom.ext
    intro a
    change faceThickRestrict k (faceThickRestrict h (toThick S a)) = faceThickRestrict (h.trans k) (toThick S a)
    rw [faceThickRestrict_base, faceThickRestrict_base, faceThickRestrict_base, thickConeRestriction_comp]
  exact RingHom.congr_fun he x

theorem faceClosedRestrict_comp {S T U : Face} (h : S ⊆ T) (k : T ⊆ U) (x : faceClosed S) :
    faceClosedRestrict k (faceClosedRestrict h x) = faceClosedRestrict (h.trans k) x := by
  have he : (faceClosedRestrict k).comp (faceClosedRestrict h) = faceClosedRestrict (h.trans k) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (ordinaryReduction (vertices S) (pivotDen S)))
    apply RingHom.ext
    intro a
    change faceClosedRestrict k (faceClosedRestrict h (toClosed S a)) = faceClosedRestrict (h.trans k) (toClosed S a)
    rw [faceClosedRestrict_base, faceClosedRestrict_base, faceClosedRestrict_base, closedConeRestriction_comp]
  exact RingHom.congr_fun he x

theorem faceReduction_restrict {S T : Face} (h : S ⊆ T) (x : faceThick S) :
    faceReduction T (faceThickRestrict h x) = faceClosedRestrict h (faceReduction S x) := by
  have he : (faceReduction T).comp (faceThickRestrict h) = (faceClosedRestrict h).comp (faceReduction S) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (pivotDen S))
    apply RingHom.ext
    intro a
    change faceReduction T (faceThickRestrict h (toThick S a)) = faceClosedRestrict h (faceReduction S (toThick S a))
    rw [faceThickRestrict_base, refinedReduction_base, refinedReduction_base, faceClosedRestrict_base,
      ordinaryReduction_restrict]
  exact RingHom.congr_fun he x

theorem faceReduction_surjective (S : Face) : Function.Surjective (faceReduction S) :=
  localReduction_surjective (ThickCone (vertices S)) (ClosedCone (vertices S)) (ordinaryReduction_surjective _) (pivotDen S)

theorem faceEpsilon_restrict {S T : Face} (h : S ⊆ T) (x : faceClosed S) :
    faceThickRestrict h ((faceCoefficients S).epsilon x) =
      (faceCoefficients T).epsilon (faceClosedRestrict h x) := by
  have h1 : faceThickRestrict h ((faceCoefficients S).epsilon 1) = (faceCoefficients T).epsilon 1 := by
    have hS := refinedCoefficients_base (vertices S) (pivotDen S) (1 : ClosedCone (vertices S))
    have hT := refinedCoefficients_base (vertices T) (pivotDen T) (1 : ClosedCone (vertices T))
    simp only [map_one] at hS hT
    rw [hS, hT, faceThickRestrict_base, ordinaryCoefficient_restrict, map_one]
  obtain ⟨z,rfl⟩ := faceReduction_surjective S x
  have hS := (faceCoefficients S).mul_epsilon z 1
  have hT := (faceCoefficients T).mul_epsilon (faceThickRestrict h z) 1
  simp only [mul_one] at hS hT
  rw [← hS, map_mul, h1, hT, faceReduction_restrict]

end CycleQ2IncidenceMarkedPivotFaces
end

#print axioms CycleQ2IncidenceMarkedPivotFaces.faceReduction_restrict
#print axioms CycleQ2IncidenceMarkedPivotFaces.faceEpsilon_restrict
