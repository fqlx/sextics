import Proposal.GeometricIncidenceMarkedPivotFaces
import Proposal.GeometricIncidenceMarkedDeformationMap
import Proposal.GeometricProjectorUnitDefect
import Proposal.GeometricSeedConeSection

/-!
# The actual image-line frames on marked pivot neighborhoods

Specialize the coordinate projector of the relative incidence matrix
and restrict it to the marked matrix-entry opens. Since the designated
entry is a unit there, its original column lifts to a frame of that
same idempotent. Frames and their pairings can then be transported to
all intersections by the genuine localization maps.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceMarkedProjectorFrames

open CycleQ2IncidenceMarkedPivotFaces CycleQ2IncidenceRelativeProjectorResidue
  CycleQ2IncidenceRelativeCechMatrix CycleQ2IncidenceMarkedDeformationMap CycleQ2GeometricRankOneImage
  CycleQ2IncidenceMarkedProjectorCharts CycleQ2IncidenceCanonicalResidue CycleQ2IncidenceEtaleParameter
  CycleQ2IncidenceEquations CycleQ2UniversalSurface CycleQ2UniversalSurfaceRestrictions
  CycleQ2GeometricSeedNormalizedCoordinates CycleQ2LiteralProjectiveIntersections
  CycleQ2GeometricUniversalSurfaceFirstOrder CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralMovingDivisorChern CycleQ2GeometricCartierNormalLift CycleQ2GeometricSeedNormalIdeals
  CycleQ2ProjectorUnitDefect

private abbrev Face := CycleQ2IncidenceMarkedPivotFaces.Face
private abbrev IndexSet := Finset (Fin 3)

def thick (S : Face) (I : IndexSet) (h : Admits (vertices S) I) : Thick I →+* faceThick S :=
  (refinedThickMap (vertices S) (pivotDen S) I h).comp (thickAtMark I)

def closed (S : Face) (I : IndexSet) (h : Admits (vertices S) I) : Local I →+* faceClosed S :=
  (refinedClosedMap (vertices S) (pivotDen S) I h).comp (closedAtMark I)

theorem reduce (S : Face) (I : IndexSet) (h : Admits (vertices S) I) (x : Thick I) :
    faceReduction S (thick S I h x) = closed S I h (reduction I x) := by
  change faceReduction S (refinedThickMap _ _ I h _) = _
  rw [refinedReduction_thickMap, thickAtMark_reduce]
  rfl

theorem epsilon (S : Face) (I : IndexSet) (h : Admits (vertices S) I) (x : Local I) :
    thick S I h ((coefficients I).epsilon x) = (faceCoefficients S).epsilon (closed S I h x) := by
  change refinedThickMap _ _ I h (thickAtMark I _) = _
  rw [thickAtMark_epsilon, refinedThickMap_coefficients]
  rfl

theorem thick_source {S : Face} {I J : IndexSet} (hIJ : I ⊆ J) (h : Admits (vertices S) J) (x : Thick I) :
    thick S J h (localSurfaceRestriction R cubic sextic test hIJ x) = thick S I (admits_subset hIJ h) x := by
  change toThick S (thickMap _ _ _ (thickAtMark J _)) = _
  rw [thickAtMark_restrict, thickMap_restrict_source]
  rfl

theorem closed_source {S : Face} {I J : IndexSet} (hIJ : I ⊆ J) (h : Admits (vertices S) J) (x : Local I) :
    closed S J h (restriction R cubic sextic hIJ x) = closed S I (admits_subset hIJ h) x := by
  change toClosed S (closedMap _ _ _ (closedAtMark J _)) = _
  rw [closedAtMark_restrict, closedMap_restrict_source]
  rfl

theorem thick_target {S T : Face} (h : S ⊆ T) (I : IndexSet) (hI : Admits (vertices S) I) (x : Thick I) :
    faceThickRestrict h (thick S I hI x) = thick T I (admits_mono (vertices_mono h) hI) x := by
  change faceThickRestrict h (toThick S (thickMap _ _ _ _)) = _
  rw [faceThickRestrict_base, thickMap_restrict_target]
  rfl

theorem closed_target {S T : Face} (h : S ⊆ T) (I : IndexSet) (hI : Admits (vertices S) I) (x : Local I) :
    faceClosedRestrict h (closed S I hI x) = closed T I (admits_mono (vertices_mono h) hI) x := by
  change faceClosedRestrict h (toClosed S (closedMap _ _ _ _)) = _
  rw [faceClosedRestrict_base, closedMap_restrict_target]
  rfl

def M (S : Face) : Entries (faceClosed S) := fun i j => toClosed S
  (algebraMap (SurfaceRing 57 1) (ClosedCone (vertices S)) (surfaceQuotient 57 1 (rawSeedMatrix (57:ℂ) i j)))

theorem M_map (S : Face) (I : IndexSet) (h : Admits (vertices S) I) : (matrix I).map (closed S I h) = M S := by
  ext i j
  change toClosed S (closedMap _ _ _ (closedAtMark I (matrix I i j))) = _
  rw [closedAtMark_eq, matrix_entry, CycleQ2IncidenceMarkedCoefficientSections.markedCone_polynomial,
    normalizedCoordinateEquiv_polynomial, CycleQ2RelativeConstantSection.pointMatrixPolynomial_seed,
    CycleQ2SeedConeSection.pointMatrixPolynomial_seed, closedMap_polynomial]
  rfl

theorem M_minors (S : Face) (i j k l : Fin 3) :
    M S i j * M S k l = M S k j * M S i l := by
  let h : Admits (vertices S) ∅ := by simp [Admits]
  rw [← M_map S ∅ h]
  simpa only [Matrix.map_apply, map_mul] using congrArg (closed S ∅ h) (matrix_minors ∅ i j k l)

private theorem singleton_admits (S : Face) (a : S) : Admits (vertices S) {a.val.1.2} := by
  intro i hi
  obtain rfl : i = a.val.1.2 := Finset.mem_singleton.mp hi
  exact ⟨a.val.1.1, Finset.mem_image_of_mem _ a.property⟩

def project (S : Face) (a : S) : Entries (faceThick S) :=
  (liftProjector a.val.1.2).map (thick S _ (singleton_admits S a))

def cert (S : Face) (a : S) (b : Fin 3 × Fin 3) : faceClosed S :=
  closed S _ (singleton_admits S a) (weights a.val.1.2 b)

theorem cert_sum (S : Face) (a : S) : ∑ b, cert S a b * M S b.1 b.2 = 1 := by
  let φ := closed S _ (singleton_admits S a)
  rw [← M_map S _ (singleton_admits S a)]
  simpa only [cert, φ, Matrix.map_apply, map_sum, map_mul, map_one] using congrArg φ (weights_sum a.val.1.2)

theorem project_idempotent (S : Face) (a : S) : IsIdempotentElem (project S a) :=
  (liftProjector_idempotent a.val.1.2).map (thick S _ (singleton_admits S a)).mapMatrix

theorem project_reduction (S : Face) (a : S) :
    (faceReduction S).mapMatrix (project S a) = projectorMatrix (M S) (cert S a) := by
  have he : (faceReduction S).mapMatrix (project S a) =
      ((reduction {a.val.1.2}).mapMatrix (liftProjector a.val.1.2)).map (closed S _ (singleton_admits S a)) := by
    ext i j
    exact reduce S _ (singleton_admits S a) _
  rw [he, liftProjector_reduction, projectorMatrix_map, M_map]
  rfl

def pivotUnit (S : Face) (a : S) : (faceClosed S)ˣ :=
  (closedPolynomialPivot_isUnit (vertices S) seedPivot S a.val a.property).unit

theorem pivotUnit_val (S : Face) (a : S) : (pivotUnit S a : faceClosed S) = M S a.val.2.1 a.val.2.2 :=
  IsUnit.unit_spec _

theorem exists_frame (S : Face) (a : S) : ∃ f : Frame (project S a),
    faceReduction S ∘ f.x = (M S).col a.val.2.2 ∧
    faceReduction S ∘ f.y = (↑(pivotUnit S a)⁻¹ : faceClosed S) •
      (projectorMatrix (M S) (cert S a)).row a.val.2.1 :=
  exists_frame_of_pivot (faceReduction S) (faceCoefficients S) (faceReduction_surjective S)
    (M S) (M_minors S) (cert S a) (cert_sum S a) a.val.2 (pivotUnit S a) (pivotUnit_val S a)
    (project S a) (project_idempotent S a) (project_reduction S a)

abbrev incl {S T : Face} (h : S ⊆ T) (a : S) : T := ⟨a.val,h a.property⟩

theorem project_restrict {S T : Face} (h : S ⊆ T) (a : S) :
    (faceThickRestrict h).mapMatrix (project S a) = project T (incl h a) := by
  ext i j
  exact thick_target h _ (singleton_admits S a) _

theorem cert_restrict {S T : Face} (h : S ⊆ T) (a : S) (b : Fin 3 × Fin 3) :
    faceClosedRestrict h (cert S a b) = cert T (incl h a) b := closed_target h _ (singleton_admits S a) _

theorem M_restrict {S T : Face} (h : S ⊆ T) (i j : Fin 3) :
    faceClosedRestrict h (M S i j) = M T i j := by rw [M, faceClosedRestrict_base, closedConeRestriction_base]; rfl

private abbrev self (a : VertexIndex) : ({a} : Face) := ⟨a,Finset.mem_singleton_self a⟩
private abbrev singleton_le {S : Face} (a : S) : {a.val} ⊆ S := Finset.singleton_subset_iff.mpr a.property

/-- Choose the generator once, on its own vertex. -/
def vertexFrame (a : VertexIndex) := (exists_frame {a} (self a)).choose

theorem vertexFrame_x (a : VertexIndex) : faceReduction {a} ∘ (vertexFrame a).x = (M {a}).col a.2.2 :=
  (exists_frame {a} (self a)).choose_spec.1

theorem vertexFrame_y (a : VertexIndex) : faceReduction {a} ∘ (vertexFrame a).y =
    (↑(pivotUnit {a} (self a))⁻¹ : faceClosed {a}) • (projectorMatrix (M {a}) (cert {a} (self a))).row a.2.1 :=
  (exists_frame {a} (self a)).choose_spec.2

/-- Use the same vertex frames on every pair and triple. -/
def faceFrame (S : Face) (a : S) : Frame (project S a) where
  x := faceThickRestrict (singleton_le a) ∘ (vertexFrame a.val).x
  y := faceThickRestrict (singleton_le a) ∘ (vertexFrame a.val).y
  normalized := ((vertexFrame a.val).map (faceThickRestrict (singleton_le a))).normalized
  eq_outer := (project_restrict (singleton_le a) (self a.val)).symm.trans
    (((vertexFrame a.val).map (faceThickRestrict (singleton_le a))).eq_outer)

theorem transition_restrict {S T : Face} (h : S ⊆ T) (a b : S) :
    faceThickRestrict h (transition (faceFrame S a) (faceFrame S b)) =
      transition (faceFrame T (incl h a)) (faceFrame T (incl h b)) := by
  unfold transition
  rw [RingHom.map_dotProduct]
  apply congrArg₂ dotProduct
  · funext i
    exact faceThickRestrict_comp (singleton_le a) h _
  · funext i
    exact faceThickRestrict_comp (singleton_le b) h _

def edgeUnit (S : Face) (a b : S) : (faceThick S)ˣ :=
  (isUnit_transition (faceReduction S) (faceCoefficients S) (faceReduction_surjective S)
    (faceFrame S a) (faceFrame S b) (by
      rw [project_reduction, project_reduction]
      exact projectorMatrix_mul (M S) (M_minors S) (cert S b) (cert_sum S b) (cert S a))).unit

theorem edgeUnit_val (S : Face) (a b : S) : (edgeUnit S a b : faceThick S) =
    transition (faceFrame S a) (faceFrame S b) := IsUnit.unit_spec _

theorem edgeUnit_restrict {S T : Face} (h : S ⊆ T) (a b : S) :
    Units.map (faceThickRestrict h).toMonoidHom (edgeUnit S a b) = edgeUnit T (incl h a) (incl h b) := by
  apply Units.ext
  change faceThickRestrict h (edgeUnit S a b : faceThick S) = (edgeUnit T (incl h a) (incl h b) : faceThick T)
  rw [edgeUnit_val, edgeUnit_val, transition_restrict]

theorem faceFrame_x (S : Face) (a : S) :
    faceReduction S ∘ (faceFrame S a).x = (M S).col a.val.2.2 := by
  funext i
  change faceReduction S (faceThickRestrict (singleton_le a) ((vertexFrame a.val).x i)) = _
  rw [faceReduction_restrict]
  exact (congrArg (faceClosedRestrict (singleton_le a)) (congrFun (vertexFrame_x a.val) i)).trans
    (M_restrict (singleton_le a) i a.val.2.2)

theorem faceFrame_y (S : Face) (a : S) :
    faceReduction S ∘ (faceFrame S a).y = (↑(pivotUnit S a)⁻¹ : faceClosed S) •
      (projectorMatrix (M S) (cert S a)).row a.val.2.1 := by
  let h := singleton_le a
  let r := faceClosedRestrict h
  have hu : Units.map r.toMonoidHom (pivotUnit {a.val} (self a.val)) = pivotUnit S a := by
    apply Units.ext
    change r (pivotUnit _ _ : faceClosed {a.val}) = (pivotUnit S a : faceClosed S)
    rw [pivotUnit_val, pivotUnit_val]
    exact M_restrict h _ _
  have hi := congrArg (fun u : (faceClosed S)ˣ => (↑(u⁻¹) : faceClosed S)) hu
  have hM : (M {a.val}).map r = M S := by ext i j; exact M_restrict h i j
  have hc : (fun q => r (cert {a.val} (self a.val) q)) = cert S a :=
    funext (cert_restrict h (self a.val))
  have hP := projectorMatrix_map r (M {a.val}) (cert {a.val} (self a.val))
  rw [hM, hc] at hP
  funext i
  change faceReduction S (faceThickRestrict h ((vertexFrame a.val).y i)) = _
  rw [faceReduction_restrict]
  have hy := congrArg r (congrFun (vertexFrame_y a.val) i)
  change r (faceReduction {a.val} ((vertexFrame a.val).y i)) =
    r ((↑(pivotUnit _ _)⁻¹ : faceClosed {a.val}) * _) at hy
  rw [map_mul] at hy
  exact hy.trans (congrArg₂ (· * ·) hi (congrArg (fun A : Entries (faceClosed S) => A a.val.2.1 i) hP))

end CycleQ2IncidenceMarkedProjectorFrames
end

#print axioms CycleQ2IncidenceMarkedProjectorFrames.M_map
#print axioms CycleQ2IncidenceMarkedProjectorFrames.exists_frame
