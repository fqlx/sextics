import Proposal.GeometricIncidenceMarkedProjectorDescent
import Proposal.GeometricIncidenceMarkedCubicTrace
import Proposal.GeometricLiteralMovingChernTrace
import Proposal.GeometricLiteralAbelJacobiMovingFaces
import Proposal.GeometricLiteralAbelJacobiRefinedLift
import Proposal.GeometricFiniteCechConnecting

/-!
# Comparing the marked projector descent with the moving divisor's Chern class

The projected triple face evaluates the regular incidence coefficient through
the two Mayer–Vietoris boundaries. Refinement to the actual pivot cover
transports its two-stage descent. A lifted-transition edge correction there
therefore compares the coefficient with the geometric Chern–cotangent cup.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceMarkedProjectorComparison

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2IncidenceMarkedCoefficientSections CycleQ2IncidenceMarkedProjectorDescent
  CycleQ2IncidenceMarkedCubicTrace CycleQ2IncidenceRelativeProjectorResidue
  CycleQ2IncidenceFirstOrderCanonicalH2 CycleQ2IncidenceEtaleParameter
  CycleQ2ProjectiveCoordinateCohomology CycleQ2ProjectiveCoordinateH2 CycleQ2CanonicalCoordinateH2
  CycleQ2ThreeOpenH2Naturality CycleQ2ThreeOpenInjectiveComparison CycleQ2CoordinateMVBinding
  CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent CycleQ2FiniteCechRefinement
  CycleQ2FiniteCechConnecting CycleQ2FiniteCechHOne CycleQ2InjectiveCech
  CycleQ2LiteralMovingDivisorChern CycleQ2LiteralAbelJacobiRefinedLift CycleQ2LiteralAbelJacobiMovingFaces
  CycleQ2SeedSectionAffineInjective CycleQ2LiteralMovingChernTrace CycleQ2SeedProjectiveImageCocycle
  CycleQ2LiteralCotangentShortExact CycleQ2CanonicalCubicDiagram CycleQ2LiteralCotangentTrace

local instance schemeHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

def markedDescent := exists_markedDescent.some

theorem markedTriple : selectedTriple coordinate markedTwo 0 1 2 = tripleSections 57 1 markedObstruction := by
  unfold selectedTriple
  rw [face_on Finset.univ ⟨0,by simp⟩ ⟨1,by simp⟩ ⟨2,by simp⟩ _ (coordinateIntersection_univ 57 1).ge]
  rfl

theorem markedClass :
    descentClass coordinate markedDescent = connectingAtTop OS (coordinate 0) (coordinate 1) (coordinate 2)
      coordinateCover (tripleSections 57 1 markedObstruction) := by
  have h := mv_eq_descent_restriction coordinate markedDescent 0 1 2
  rw [markedTriple] at h
  let e := ((OS.cohomologyPresheaf 2).mapIso (eqToIso coordinateCover.symm).op).addCommGroupIsoToAddEquiv
  exact ((congrArg e h).trans (coverIso_restriction OS _ coordinateCover _)).symm

def pivot_le (i : VertexIndex) : pivotCover i ≤ coordinate i.1.2 := by
  refine inf_le_left.trans ((cover_le_patch i.1).trans ?_)
  rcases i with ⟨⟨v,j⟩,p⟩
  fin_cases j <;> exact le_rfl

def pivotTwo := restrictTwo coordinate pivotCover (fun i => i.1.2) pivot_le markedTwo

private theorem moving_descent (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    ∃ d : TwoDescent pivotCover (movingCup t ht),
      (movingClass t ht).comp cotangentAdditiveShortExact.extClass rfl = descentClass pivotCover d := by
  let α := logOne (movingSystem t ht)
  let b := edgeLift pivotCover parentVertex pivot_le_native α
  obtain ⟨d, hd⟩ := exists_descent_of_lift pivotCover cotangentAdditiveShortExact pivotCover_covers b
    (movingCup t ht) (edgeLift_boundary pivotCover parentVertex pivot_le_native α (logOne_closed _))
  refine ⟨d, ?_⟩
  have he := edgeLift_reduce pivotCover parentVertex pivot_le_native α
  have hu : ∀ (c c' : One _ pivotCover) (e : c = c') (hc : IsOneCocycle _ _ c)
      (hc' : IsOneCocycle _ _ c'), cechOneClass pivotCover pivotCover_covers c hc =
        cechOneClass pivotCover pivotCover_covers c' hc' := by
    rintro c _ rfl _ _
    rfl
  rw [hu _ _ he _ (logOne_closed _)] at hd
  exact hd

theorem marked_trace_of_edge_correction (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (b : One OS pivotCover)
    (hb : ∀ i j k W hi hj hk, boundaryValue OS pivotCover b i j k W hi hj hk =
      faceValue OS pivotCover (pivotTwo - movingCup t ht) i j k W hi hj hk) :
    seedMap regularCoefficient = algebraicTrace (cubicH2 firstOrderWeightedCubic
      ((movingClass t ht).comp cotangentAdditiveShortExact.extClass rfl)) := by
  obtain ⟨d, hd⟩ := moving_descent t ht
  let e := restrictDescent coordinate pivotCover (fun i => i.1.2) pivot_le markedDescent
  have h0 := descentClass_eq_zero_of_boundary pivotCover pivotCover_covers (subtractDescents pivotCover e d) b hb
  rw [descentClass_sub] at h0
  have hclass : descentClass coordinate markedDescent = (movingClass t ht).comp cotangentAdditiveShortExact.extClass rfl :=
    (sub_eq_zero.mp h0).trans hd.symm
  rw [regularCoefficient_trace, ← cubicH2_coordinateConnecting, ← markedClass, hclass]

end CycleQ2IncidenceMarkedProjectorComparison
end

#print axioms CycleQ2IncidenceMarkedProjectorComparison.marked_trace_of_edge_correction
