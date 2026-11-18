import Proposal.GeometricIncidenceMarkedProjectorFrames
import Proposal.GeometricProjectorCochainSpecialization
import Proposal.GeometricProjectorTransitionComparison

/-!
# The relative obstruction on every marked matrix-pivot face

On the genuine marked intersections the specialized projector obstruction
is the square-zero coefficient of the unit defect of the chosen column
frames. This formula uses the same edge unit on every incident face.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceMarkedTransitionFaces

open CycleQ2IncidenceMarkedProjectorFrames CycleQ2IncidenceMarkedPivotFaces
  CycleQ2IncidenceRelativeProjectorResidue CycleQ2IncidenceRelativeCechMatrix
  CycleQ2IncidenceMarkedProjectorCharts CycleQ2IncidenceCanonicalResidue
  CycleQ2LiteralMovingDivisorChern CycleQ2GeometricUniversalSurfaceFirstOrder
  CycleQ2ProjectorCochainSpecialization CycleQ2ProjectorUnitDefect
  CycleQ2ProjectorTransitionComparison CycleQ2GeometricRankOneImage

private abbrev Face := CycleQ2IncidenceMarkedPivotFaces.Face
def coordinateIndices (S : Face) : Finset (Fin 3) := S.image (fun a => a.1.2)
def index {S : Face} (a : S) : coordinateIndices S := ⟨a.val.1.2, Finset.mem_image_of_mem _ a.property⟩
theorem admits (S : Face) : Admits (vertices S) (coordinateIndices S) := by
  intro i hi
  obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hi
  exact ⟨a.1.1, Finset.mem_image_of_mem _ ha⟩

private abbrev sourceCert (S : Face) (a : S) := restrictedWeights (coordinateIndices S) (index a)
private abbrev sourceProject (S : Face) (a : S) := restrictedProjector (coordinateIndices S) (index a)

private theorem cert_map (S : Face) (a : S) (q : Fin 3 × Fin 3) :
    closed S (coordinateIndices S) (admits S) (sourceCert S a q) = cert S a q :=
  closed_source (Finset.singleton_subset_iff.mpr (index a).property) (admits S) _

private theorem project_map (S : Face) (a : S) :
    (sourceProject S a).map (thick S (coordinateIndices S) (admits S)) = project S a := by
  ext i j
  exact thick_source (Finset.singleton_subset_iff.mpr (index a).property) (admits S) _

theorem reduced_edges (S : Face) (a b c : S) :
    reduceUnit (faceReduction S) (edgeUnit S a b) * reduceUnit (faceReduction S) (edgeUnit S b c) =
      reduceUnit (faceReduction S) (edgeUnit S a c) := by
  apply Units.ext
  change faceReduction S (edgeUnit S a b : faceThick S) * faceReduction S (edgeUnit S b c : faceThick S) =
    faceReduction S (edgeUnit S a c : faceThick S)
  rw [edgeUnit_val, edgeUnit_val, edgeUnit_val]
  apply transition_reduced_mul
  rw [project_reduction, project_reduction]
  exact projectorMatrix_mul (M S) (M_minors S) (cert S b) (cert_sum S b) (cert S c)

def unitFace (S : Face) (a b c : S) := face (edgeUnit S a b) (edgeUnit S b c) (edgeUnit S a c) (reduced_edges S a b c)

theorem obstruction_eq_kernelLog (S : Face) (a b c : S) :
    closed S (coordinateIndices S) (admits S) (obstruction (coordinateIndices S) (index a) (index b) (index c)) =
      (kernelLog (faceCoefficients S) (unitFace S a b c)).toAdd := by
  let I := coordinateIndices S
  let φ := closed S I (admits S)
  let ψ := thick S I (admits S)
  have hsum (i : S) : ∑ q, sourceCert S i q * matrix I q.1 q.2 = 1 :=
    weights_restrict_sum i.val.1.2 (index i).property
  have he := scalarCochain_map (coefficients I) (faceCoefficients S) ψ φ (epsilon S I (admits S))
    (matrix I) (matrix_minors I) (sourceCert S) hsum (sourceProject S)
    (fun i => restrictedProjector_reduction I (index i))
    (M S) (M_minors S) (cert S) (cert_sum S) (project S) (project_reduction S)
    (M_map S I (admits S)) (project_map S) (sourceCert S a) a b c
  have hw : (fun q => φ (sourceCert S a q)) = cert S a := funext (cert_map S a)
  rw [hw] at he
  exact he.trans (scalarCochain_eq_transitionCoefficient (faceReduction S) (faceCoefficients S)
    (M S) (M_minors S) (cert S) (cert_sum S) (project S) (project_reduction S) (cert S a) (cert_sum S a)
    a b c (faceFrame S a) (faceFrame S b) (faceFrame S c) (edgeUnit S a b) (edgeUnit S b c) (edgeUnit S a c)
    (edgeUnit_val S a b) (edgeUnit_val S b c) (edgeUnit_val S a c) _
    (epsilon_kernelLog (faceCoefficients S) (unitFace S a b c)))

end CycleQ2IncidenceMarkedTransitionFaces
end

#print axioms CycleQ2IncidenceMarkedTransitionFaces.obstruction_eq_kernelLog
