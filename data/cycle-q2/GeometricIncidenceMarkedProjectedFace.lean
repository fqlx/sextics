import Proposal.GeometricIncidenceMarkedFaceProjection
import Proposal.GeometricIncidenceMarkedProjectorComparison
import Proposal.GeometricIncidenceMarkedTransitionFaces
import Proposal.GeometricCommonOpenDegreeProjection

/-!
# The specialized Laurent obstruction on the actual projective pivot face

Restricting the marked coordinate representative to a pivot face and
projecting the corresponding cone element there give the same regular
function. Thus its value is the projected kernel logarithm of the
transition units of the actual relative projector.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceMarkedProjectedFace

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2IncidenceMarkedPivotFaces CycleQ2IncidenceMarkedFaceProjection
  CycleQ2IncidenceMarkedTransitionFaces CycleQ2IncidenceMarkedProjectorCharts
  CycleQ2IncidenceMarkedProjectorFrames CycleQ2IncidenceMarkedProjectorComparison
  CycleQ2IncidenceMarkedCoefficientSections CycleQ2IncidenceMarkedProjectorDescent
  CycleQ2IncidenceMarkedDeformationMap CycleQ2LiteralMovingDivisorChern
  CycleQ2GeometricSurfaceCoordinates CycleQ2GeometricSeedNormalIdeals CycleQ2GeometricCartierNormalLift
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionProjection CycleQ2LiteralMovingPivotPrincipal
  CycleQ2GeometricSeedNormalizedCoordinates CycleQ2CartierSurfaceGrading CycleQ2ProjectiveCoordinateCohomology
  CycleQ2FiniteCechRefinement CycleQ2FiniteInjectiveCech CycleQ2ProjectorTransitionComparison
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso

private abbrev Face := CycleQ2IncidenceMarkedPivotFaces.Face
private abbrev X := CycleQ2IncidenceMarkedCoefficientSections.Surface

private def coneMap (s : Finset Vertex) (I : Finset (Fin 3)) (h : Admits s I) :
    CoordinateLocal 57 1 I →ₐ[SurfaceRing 57 1] ClosedCone s where
  toRingHom := (closedMap s I h).comp (normalizedCoordinateEquiv 57 I).toRingHom
  commutes' x := by
    obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
    change closedMap s I h (normalizedCoordinateEquiv 57 I (algebraMap _ _ (quotientMap 57 1 p))) = _
    rw [normalizedCoordinateEquiv_polynomial, closedMap_polynomial]
    rfl

theorem face_le_coordinate (S : Face) (hS : S.Nonempty) (I : Finset (Fin 3)) (h : Admits (vertices S) I) :
    faceOpen S hS ≤ openOf I := by
  apply le_openOf
  intro i hi
  obtain ⟨v,hv⟩ := h i hi
  obtain ⟨a,ha,he⟩ := Finset.mem_image.mp hv
  have he' : a.1.2 = i := congrArg Prod.snd he
  rw [← he', faceOpen_eq]
  exact (Finset.inf_le (f := pivotCover) ha).trans (pivot_le a)

theorem projected_coordinate (S : Face) (hS : S.Nonempty) (I : Finset (Fin 3)) (hI : I.Nonempty)
    (h : Admits (vertices S) I) (x : CycleQ2IncidenceMarkedCoefficientSections.Local I) :
    faceProjection S hS (closed S I h x) =
      onOpen I hI (faceOpen S hS) (face_le_coordinate S hS I h) x := by
  change faceProjection S hS (toClosed S (closedMap _ _ _ (closedAtMark I x))) = _
  rw [closedAtMark_eq, faceProjection_base]
  change closedPrincipalEquiv _ _ _ (algebraMap _ _ _) = _
  rw [closedPrincipalEquiv_base]
  exact CycleQ2CommonOpenDegreeProjection.commonOpen (surfaceGrade 57 1)
    (coordinateProduct_mem_grade 57 1 I) (closedProduct_homogeneous (vertices S))
    (coneMap (vertices S) I h) (faceOpen S hS) (face_le_coordinate S hS I h)
    (principalOpen_le _ _ _) (markedCone I x)

private theorem face_le_vertex (S : Face) (hS : S.Nonempty) (a : S) :
    faceOpen S hS ≤ pivotCover a.val := by rw [faceOpen_eq]; exact Finset.inf_le a.property

theorem projected_unit_face (S : Face) (hS : S.Nonempty) (a b c : S) :
    faceProjection S hS (kernelLog (faceCoefficients S) (unitFace S a b c)).toAdd =
      faceValue OS pivotCover pivotTwo a.val b.val c.val (faceOpen S hS)
        (face_le_vertex S hS a) (face_le_vertex S hS b) (face_le_vertex S hS c) := by
  rw [← obstruction_eq_kernelLog, projected_coordinate S hS _ ⟨_,(index a).property⟩]
  symm
  rw [pivotTwo, faceValue_restrictTwo]
  exact face_on (coordinateIndices S) (index a) (index b) (index c) (faceOpen S hS)
    (face_le_coordinate S hS _ (admits S)) _ _ _

end CycleQ2IncidenceMarkedProjectedFace
end

#print axioms CycleQ2IncidenceMarkedProjectedFace.projected_unit_face
