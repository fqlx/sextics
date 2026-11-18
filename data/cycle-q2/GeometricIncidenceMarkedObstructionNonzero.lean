import Proposal.GeometricIncidenceMarkedProjectorGauge
import Proposal.GeometricIncidenceMarkedSplitFaces
import Proposal.GeometricIncidenceMarkedCorrectionDescent
import Proposal.GeometricIncidenceMarkedProjectedFace

/-!
# The nonzero incidence obstruction at the marked sextic

The logarithm of the quotient of two lifted transitions is a regular
function on each pivot overlap. Its Čech boundary is the difference
between the projector obstruction and the moving Chern–cotangent cup.
The normalized coefficient of the relative incidence obstruction therefore
specializes to the previously computed nonzero cubic trace.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceMarkedObstructionNonzero

open CategoryTheory AlgebraicGeometry CycleQ2SeedSectionAffineInjective
  CycleQ2IncidenceMarkedPivotFaces CycleQ2IncidenceMarkedProjectorFrames
  CycleQ2IncidenceMarkedProjectorGauge CycleQ2IncidenceMarkedFaceProjection
  CycleQ2IncidenceMarkedSplitFaces CycleQ2IncidenceMarkedCorrectionDescent
  CycleQ2IncidenceMarkedTransitionFaces CycleQ2IncidenceMarkedProjectedFace
  CycleQ2IncidenceMarkedProjectorComparison CycleQ2IncidenceMarkedCoefficientSections
  CycleQ2IncidenceRelativeProjectorResidue CycleQ2IncidenceEtaleParameter CycleQ2IncidenceFirstOrderCanonicalH2
  CycleQ2ProjectorTransitionComparison CycleQ2FiniteInjectiveCech CycleQ2FiniteCechRefinement
  CycleQ2LiteralMovingChernTrace CycleQ2LiteralMovingDivisorChern CycleQ2LiteralAbelJacobiMovingFaces
  CycleQ2LiteralCotangentShortExact CycleQ2CanonicalCubicDiagram CycleQ2LiteralCotangentTrace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
private abbrev Faces := CycleQ2IncidenceMarkedPivotFaces.Face

private abbrev split (S : Faces) (hS : S.Nonempty) (a b : S) :=
  splitEdge t ht S hS a.val b.val a.property b.property

theorem sameReduction (S : Faces) (hS : S.Nonempty) (a b : S) :
    reduceUnit (faceReduction S) (gaugedEdge S a b) = reduceUnit (faceReduction S) (split t ht S hS a b) :=
  (gaugedEdge_reduction t ht S hS a b).trans (splitEdge_reduction t ht S hS _ _ _ _).symm

private def quotientUnit (S : Faces) (hS : S.Nonempty) (a b : S) :=
  edge (gaugedEdge S a b) (split t ht S hS a b) (sameReduction t ht S hS a b)

def correction : EdgeData := fun S hS a b =>
  faceProjection S hS (kernelLog (faceCoefficients S) (quotientUnit t ht S hS a b)).toAdd

theorem correction_natural : Natural (correction t ht) := by
  intro S T h hS hT a b
  change sectionRestrict h hS hT (faceProjection S hS _) = faceProjection T hT _
  rw [faceProjection_restrict]
  apply congrArg (faceProjection T hT)
  apply Eq.symm
  apply kernelLog_map (faceCoefficients S) (faceCoefficients T) (faceThickRestrict h) (faceClosedRestrict h)
    (faceEpsilon_restrict h)
  have he : Units.map (faceThickRestrict h).toMonoidHom (quotientUnit t ht S hS a b).val =
      (quotientUnit t ht T hT (incl h a) (incl h b)).val := by
    change Units.map (faceThickRestrict h).toMonoidHom
      (gaugedEdge S a b * (split t ht S hS a b)⁻¹) = _
    rw [map_mul, map_inv, gaugedEdge_restrict]
    unfold split
    rw [splitEdge_restrict]
    rfl
  exact congrArg Units.val he.symm

theorem correction_boundary : Boundary (correction t ht) (pivotTwo - movingCup t ht) := by
  intro S hS a b c
  let u := gaugedEdge S a b
  let v := gaugedEdge S b c
  let w := gaugedEdge S a c
  let u' := split t ht S hS a b
  let v' := split t ht S hS b c
  let w' := split t ht S hS a c
  have h' : reduceUnit (faceReduction S) u' * reduceUnit (faceReduction S) v' =
       reduceUnit (faceReduction S) w' := splitFace_cocycle t ht S hS _ _ _ _ _ _
  have h : reduceUnit (faceReduction S) u * reduceUnit (faceReduction S) v = reduceUnit (faceReduction S) w := by
    rw [sameReduction t ht S hS a b, sameReduction t ht S hS b c, sameReduction t ht S hS a c]
    exact h'
  have he := congrArg (faceProjection S hS) (face_change (faceCoefficients S) u v w u' v' w' h
    (sameReduction t ht S hS a b) (sameReduction t ht S hS b c) (sameReduction t ht S hS a c))
  simp only [map_sub, map_add] at he
  rw [show face u v w h = unitFace S a b c from gaugedFace S a b c h, projected_unit_face,
    splitFace_projection] at he
  refine he.symm.trans ?_
  exact (map_sub (res OS _) _ _).symm

theorem regularCoefficient_at_mark :
    seedMap regularCoefficient = algebraicTrace (cubicH2 firstOrderWeightedCubic
      ((movingClass t ht).comp cotangentAdditiveShortExact.extClass rfl)) :=
  marked_trace_of_face_correction t ht (correction t ht) (correction_natural t ht) (correction_boundary t ht)

theorem regularCoefficient_at_mark_ne_zero : seedMap regularCoefficient ≠ 0 := by
  obtain ⟨s,hs,_⟩ := exists_flat_moving_curve_with_nonzero_trace (1 : MvPolynomial (Fin 3) ℂ) one_ne_zero
  rw [regularCoefficient_at_mark s hs]
  exact movingClass_cubic_trace_ne_zero s hs

end CycleQ2IncidenceMarkedObstructionNonzero
end

#print axioms CycleQ2IncidenceMarkedObstructionNonzero.regularCoefficient_at_mark_ne_zero
