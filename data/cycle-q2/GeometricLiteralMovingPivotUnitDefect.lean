import Proposal.GeometricLiteralMovingPivotDifferential
import Proposal.GeometricMovingPivotRingSplittings
import Proposal.GeometricLiteralMovingResidueConnecting

/-!
# Obstruction of arbitrary lifts of the actual moving transitions

On a moving pivot face the multiplicative defect equals the actual
Kodaira–Spencer evaluation of the moving Chern edge plus the three
edge corrections. Both the reduction and the epsilon coefficient are
taken in the localized original ambient-test deformation.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingPivotUnitDefect

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  CycleQ2GeometricKernelLocalization CycleQ2GeometricSquareZeroSplittings
  CycleQ2MovingPivotRingSplittings CycleQ2LiteralMovingPivotPrincipal
  CycleQ2LiteralMovingPivotDifferential CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2InjectiveCech CycleQ2FiniteCechDescent CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionKernel CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralNativeChernCocycle
  CycleQ2LiteralNativeKodairaSpencer CycleQ2LiteralNativeKodairaSpencerCocycle
  CycleQ2LiteralNativeTangentEvaluation CycleQ2LiteralNativeDifferentialSections
  CycleQ2LiteralMovingDivisorChern CycleQ2LiteralAbelJacobiMovingFaces
  CycleQ2LiteralAbelJacobiRefinedCup CycleQ2LiteralAbelJacobiRefinedLift
  CycleQ2LiteralCotangentShortExact CycleQ2SeedSectionAffineInjective

open CycleQ2CechTwoToDerived (app)
attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower
  CycleQ2GeometricKernelLocalization.localReductionAlgebra

variable (s : Finset Vertex) (hs : s.Nonempty) (p : ThickRing s)
abbrev E := ThickAt (ThickRing s) p
abbrev C := ClosedAt (ThickRing s) (ClosedRing s) p
abbrev kernelChart := localizedKernelEquiv (ThickRing s) (ClosedRing s) (epsilonKernelEquiv s) p

def correction (a : VertexIndex) (ha : a.1 ∈ s) (g : (E s p)ˣ) : C s p :=
  unitCorrection (kernelChart s p)
    (localizedSplit (epsilonKernelEquiv s) p (projectiveSplittingAlgHom s a.1.1 ⟨a.1.2,ha⟩)
      (projectiveSplittingAlgHom_reduction s a.1.1 ⟨a.1.2,ha⟩))
    (localizedSplit_reduction _ _ _ _) g

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
  (a b c : VertexIndex) (ha : a.1 ∈ s) (hb : b.1 ∈ s)
  (W : Surface.Opens) (hW : W ≤ principalOpen s hs (nativeReduction s p))
  (haW : W ≤ pivotCover a) (hbW : W ≤ pivotCover b) (hcW : W ≤ pivotCover c)
  (u v w : (E s p)ˣ) (h : reducedUnit (C := C s p) u * reducedUnit v = reducedUnit w)

abbrev sectionValue := value s hs (nativeReduction s p) W hW

theorem arbitraryLift_face
    (hv : Units.map (sectionValue s hs p W hW).toMonoidHom (reducedUnit v) =
      (movingSystem t ht).value (frameAt b W hbW) (frameAt c W hcW)) :
    sectionValue s hs p W hW (unitDefect (kernelChart s p) u v w h) =
      sectionValue s hs p W hW (correction s p b hb v - correction s p a ha w + correction s p a ha u) +
      (show Γ(Surface,W) from faceValue coefficientSheaf pivotCover (movingCup t ht) a b c W haW hbW hcW) := by
  let σ := projectiveSplittingAlgHom s a.1.1 ⟨a.1.2,ha⟩
  let τ := projectiveSplittingAlgHom s b.1.1 ⟨b.1.2,hb⟩
  let hσ := projectiveSplittingAlgHom_reduction s a.1.1 ⟨a.1.2,ha⟩
  let hτ := projectiveSplittingAlgHom_reduction s b.1.1 ⟨b.1.2,hb⟩
  have hd := localizedUnitDefect (epsilonKernelEquiv s) p σ τ hσ hτ u v w h
  rw [hd, map_add]
  apply congrArg (_ + ·)
  rw [scalarCup_face]
  unfold scalarValue
  rw [logOne_common, ← hv, kodairaSpencerValue_common s hs a.1 b.1 ha hb W
    (hW.trans (principalOpen_le s hs (nativeReduction s p)))]
  exact (value_log s hs (nativeReduction s p) W hW (vertexKodairaSpencer s a.1 b.1 ha hb)
    (reducedUnit (C := C s p) v)).symm

/-- The actual ambient-test cotangent boundary of the moving divisor has
the arbitrary lift defect for its epsilon coefficient, after removing the
three normalized edge corrections. -/
theorem arbitraryLift_cotangent_boundary
    (hv : Units.map (sectionValue s hs p W hW).toMonoidHom (reducedUnit v) =
      (movingSystem t ht).value (frameAt b W hbW) (frameAt c W hcW)) :
    boundaryValue cotangentAdditiveComplex.X₂ pivotCover
      (edgeLift pivotCover parentVertex pivot_le_native (logOne (movingSystem t ht))) a b c W haW hbW hcW =
    app cotangentAdditiveComplex.f W
      (sectionValue s hs p W hW (unitDefect (kernelChart s p) u v w h) -
       sectionValue s hs p W hW (correction s p b hb v - correction s p a ha w + correction s p a ha u)) := by
  rw [edgeLift_boundary _ _ _ _ (logOne_closed _)]
  apply congrArg (app cotangentAdditiveComplex.f W)
  have he := arbitraryLift_face s hs p t ht a b c ha hb W hW haW hbW hcW u v w h hv
  rw [he, add_sub_cancel_left]

section FullFace

variable (i j k : VertexIndex)

abbrev liftDenominator := nativeLift (vertices i j k) (pivotProduct i j k)

theorem actualFace_le : face i j k ≤ principalOpen (vertices i j k) (inhabitedVertices i j k)
    (nativeReduction _ (liftDenominator i j k)) := by
  rw [nativeLift_reduction, pivotProduct_open]

abbrev faceValueMap := sectionValue (vertices i j k) (inhabitedVertices i j k) (liftDenominator i j k)
  (face i j k) (actualFace_le i j k)

/-- Specialization with the entire Čech triple, concrete native thick
denominator and its genuine coordinate-ring splitting. -/
theorem entireMovingFace (u v w : (E (vertices i j k) (liftDenominator i j k))ˣ)
    (h : reducedUnit (C := C (vertices i j k) (liftDenominator i j k)) u * reducedUnit v = reducedUnit w)
    (hv : Units.map (faceValueMap i j k).toMonoidHom (reducedUnit v) =
      (movingSystem t ht).value (frameAt j (face i j k) (inf_le_left.trans inf_le_right)) (frameAt k _ inf_le_right)) :
    boundaryValue cotangentAdditiveComplex.X₂ pivotCover
      (edgeLift pivotCover parentVertex pivot_le_native (logOne (movingSystem t ht))) i j k (face i j k)
        (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right =
      app cotangentAdditiveComplex.f (face i j k)
        (faceValueMap i j k (unitDefect (kernelChart (vertices i j k) (liftDenominator i j k)) u v w h) -
          faceValueMap i j k
            (correction (vertices i j k) (liftDenominator i j k) j (by simp [vertices]) v -
             correction (vertices i j k) (liftDenominator i j k) i (by simp [vertices]) w +
             correction (vertices i j k) (liftDenominator i j k) i (by simp [vertices]) u)) :=
  arbitraryLift_cotangent_boundary (vertices i j k) (inhabitedVertices i j k) (liftDenominator i j k)
    t ht i j k (by simp [vertices]) (by simp [vertices]) (face i j k) (actualFace_le i j k)
    (inf_le_left.trans inf_le_left) (inf_le_left.trans inf_le_right) inf_le_right u v w h hv

end FullFace

end CycleQ2LiteralMovingPivotUnitDefect
end

#print axioms CycleQ2LiteralMovingPivotUnitDefect.arbitraryLift_face
#print axioms CycleQ2LiteralMovingPivotUnitDefect.arbitraryLift_cotangent_boundary

#print axioms CycleQ2LiteralMovingPivotUnitDefect.entireMovingFace
