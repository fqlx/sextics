import Proposal.GeometricIncidenceMarkedTransitionFaces
import Proposal.GeometricIncidenceMarkedFaceProjection
import Proposal.GeometricProjectorMappedPivot

/-!
# Lifted moving-divisor transitions on the marked faces

The homogeneous columns give local frames of the marked projector. Its
transition ratio uses the pivot-normalized generator. Multiplying by a
lift of the native pivot at each vertex gives the moving-divisor
transition on reduction and preserves the product on each triple.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1600000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceMarkedProjectorGauge

open CategoryTheory AlgebraicGeometry CycleQ2IncidenceMarkedPivotFaces
  CycleQ2IncidenceMarkedFaceProjection CycleQ2IncidenceMarkedProjectorFrames
  CycleQ2IncidenceMarkedTransitionFaces CycleQ2LiteralMovingDivisorChern
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedProjectiveImageCocycle
  CycleQ2LiteralNativeCartierFrames CycleQ2IncidenceMarkedProjectorCharts
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralMovingPivotPrincipal
  CycleQ2ProjectorTransitionComparison CycleQ2ProjectorUnitDefect CycleQ2SeedSectionAffineInjective

private abbrev Faces := CycleQ2IncidenceMarkedPivotFaces.Face

theorem within {S : Faces} (hS : S.Nonempty) (a : S) : faceOpen S hS ≤ pivotCover a.val := by
  rw [faceOpen_eq]
  exact Finset.inf_le a.property

abbrev chartFrame (S : Faces) (hS : S.Nonempty) (a : S) := frameAt a.val _ (within hS a)

def coordinateScale (S : Faces) (a : S) : (faceClosed S)ˣ :=
  Units.map (toClosed S).toMonoidHom ((closedCoordinateValue_isUnit _ a.val.1 (vertex_mem a.property)).pow 14).unit

theorem matrix_scaled (S : Faces) (hS : S.Nonempty) (a : S) :
    M S = (coordinateScale S a : faceClosed S) •
      (sectionMatrix (chartFrame S hS a).chart (faceOpen S hS) (chartFrame S hS a).within).map
        (nativeToFace S hS) := by
  ext i j
  let k : VertexIndex := (a.val.1,(i,j))
  let V := CycleQ2IncidenceMarkedPivotFaces.vertices S
  have hv : k.1 ∈ V := vertex_mem a.property
  let q := pivotEntry V (vertices_nonempty hS) k hv
  have hs : nativeSection S hS q =
      sectionMatrix (chartFrame S hS a).chart (faceOpen S hS) (chartFrame S hS a).within i j := by
    change closedPrincipalEquiv V _ _ (algebraMap _ _ q) = _
    rw [closedPrincipalEquiv_base, pivotEntry_section]
    exact sectionMatrix_restrict _ _ _ _ _
  have hx : q.val * closedCoordinateValue V k.1 ^ 14 =
      algebraMap _ (ClosedCone V) (CycleQ2GeometricCartierNormalLift.surfaceQuotient 57 1
        (CycleQ2IncidenceMarkedNativeCharts.seedPivot k)) := by
    dsimp only [q]
    rw [CycleQ2IncidenceMarkedNativeCharts.pivotEntry_eq_normalized]
    exact (reduction_normalized_mul V k.1 hv _ _).trans
      (congrArg (algebraMap _ (ClosedCone V)) (CycleQ2LiteralGradedReduction.reduction_polynomial _))
  change M S i j = (coordinateScale S a : faceClosed S) *
    nativeToFace S hS (sectionMatrix _ _ _ i j)
  rw [← hs, nativeToFace_base]
  change toClosed S _ = toClosed S (↑((closedCoordinateValue_isUnit V k.1 hv).pow 14).unit : ClosedCone V) *
    toClosed S q.val
  rw [IsUnit.unit_spec, ← map_mul, mul_comm]
  exact congrArg (toClosed S) hx.symm

theorem reduced_raw (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (S : Faces) (hS : S.Nonempty) (a b : S) :
    reduceUnit (faceReduction S) (edgeUnit S a b) =
      Units.map (nativeToFace S hS).toMonoidHom
        ((movingSystem t ht).value (chartFrame S hS a) (chartFrame S hS b) *
          (chartFrame S hS b).pivotUnit * (chartFrame S hS a).pivotUnit⁻¹) :=
  CycleQ2ProjectorMappedPivot.transition_reduction_mapped_movingSystem t ht _ _ _ (M S)
    (coordinateScale S a) (pivotUnit S a) (matrix_scaled S hS a) (pivotUnit_val S a)
    (faceReduction S) (cert S a) (cert_sum S a) (faceFrame S a) (faceFrame S b) (faceFrame_y S a)
    (faceFrame_x S b) (edgeUnit S a b) (edgeUnit_val S a b)

def nativePivot (S : Faces) (hS : S.Nonempty) (a : S) : (faceClosed S)ˣ :=
  Units.map (nativeToFace S hS).toMonoidHom (chartFrame S hS a).pivotUnit

theorem nativePivot_restrict {S T : Faces} (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty) (a : S) :
    Units.map (faceClosedRestrict h).toMonoidHom (nativePivot S hS a) = nativePivot T hT (incl h a) := by
  apply Units.ext
  change faceClosedRestrict h (nativeToFace S hS _) = nativeToFace T hT _
  rw [nativeToFace_restrict]
  apply congrArg (nativeToFace T hT)
  rw [(chartFrame S hS a).pivot_eq, (chartFrame T hT (incl h a)).pivot_eq]
  exact sectionMatrix_restrict _ _ _ _ _

private abbrev single (a : VertexIndex) : ({a} : Faces) := ⟨a,Finset.mem_singleton_self a⟩
private abbrev one_le {S : Faces} (a : S) : {a.val} ⊆ S := Finset.singleton_subset_iff.mpr a.property

private theorem exists_vertexUnit (a : VertexIndex) : ∃ u : (faceThick {a})ˣ,
    reduceUnit (faceReduction {a}) u = nativePivot {a} (Finset.singleton_nonempty a) (single a) := by
  let v := nativePivot {a} (Finset.singleton_nonempty a) (single a)
  obtain ⟨x,hx⟩ := faceReduction_surjective {a} (v : faceClosed {a})
  have hu := isUnit_of_reduced_unit (faceReduction {a}) (faceCoefficients {a}) (faceReduction_surjective {a})
    x (by rw [hx]; exact v.isUnit)
  exact ⟨hu.unit, Units.ext ((congrArg (faceReduction {a}) hu.unit_spec).trans hx)⟩

def vertexUnit (S : Faces) (a : S) : (faceThick S)ˣ :=
  Units.map (faceThickRestrict (one_le a)).toMonoidHom (exists_vertexUnit a.val).choose

theorem vertexUnit_reduced (S : Faces) (hS : S.Nonempty) (a : S) :
    reduceUnit (faceReduction S) (vertexUnit S a) = nativePivot S hS a := by
  apply Units.ext
  change faceReduction S (faceThickRestrict (one_le a) _) = (nativePivot S hS a : faceClosed S)
  rw [faceReduction_restrict]
  exact (congrArg (faceClosedRestrict (one_le a)) (congrArg Units.val (exists_vertexUnit a.val).choose_spec)).trans
    (congrArg Units.val (nativePivot_restrict (one_le a) _ hS (single a.val)))

theorem vertexUnit_restrict {S T : Faces} (h : S ⊆ T) (a : S) :
    Units.map (faceThickRestrict h).toMonoidHom (vertexUnit S a) = vertexUnit T (incl h a) :=
  Units.ext (faceThickRestrict_comp (one_le a) h _)

def gaugedEdge (S : Faces) (a b : S) : (faceThick S)ˣ := vertexUnit S a * edgeUnit S a b * (vertexUnit S b)⁻¹

theorem gaugedEdge_restrict {S T : Faces} (h : S ⊆ T) (a b : S) :
    Units.map (faceThickRestrict h).toMonoidHom (gaugedEdge S a b) = gaugedEdge T (incl h a) (incl h b) := by
  simp only [gaugedEdge, map_mul, map_inv, vertexUnit_restrict, edgeUnit_restrict]

theorem gaugedEdge_reduction (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (S : Faces) (hS : S.Nonempty) (a b : S) :
    reduceUnit (faceReduction S) (gaugedEdge S a b) = Units.map (nativeToFace S hS).toMonoidHom
      ((movingSystem t ht).value (chartFrame S hS a) (chartFrame S hS b)) := by
  rw [gaugedEdge, map_mul, map_mul, map_inv, vertexUnit_reduced _ hS, vertexUnit_reduced _ hS,
    reduced_raw t ht S hS]
  simp only [nativePivot, map_mul, map_inv]
  group <;> ac_rfl

theorem gaugedFace (S : Faces) (a b c : S)
    (h : reduceUnit (faceReduction S) (gaugedEdge S a b) * reduceUnit (faceReduction S) (gaugedEdge S b c) =
      reduceUnit (faceReduction S) (gaugedEdge S a c)) :
    face (gaugedEdge S a b) (gaugedEdge S b c) (gaugedEdge S a c) h = unitFace S a b c := by
  apply Subtype.ext
  change gaugedEdge S a b * gaugedEdge S b c * (gaugedEdge S a c)⁻¹ =
    edgeUnit S a b * edgeUnit S b c * (edgeUnit S a c)⁻¹
  unfold gaugedEdge
  group <;> ac_rfl

end CycleQ2IncidenceMarkedProjectorGauge
end

#print axioms CycleQ2IncidenceMarkedProjectorGauge.gaugedEdge_reduction
