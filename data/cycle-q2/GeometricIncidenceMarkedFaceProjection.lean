import Mathlib.Algebra.BigOperators.Associated
import Proposal.GeometricIncidenceMarkedPivotFaces
import Proposal.GeometricIncidenceMarkedNativeCharts
import Proposal.GeometricPrincipalProjectionLocalization

/-!
# Weight-zero projection onto the actual moving pivot faces

The raw seed pivots differ from their native projective chart entries by
units in the spatial coordinate frames. Localizing the linear projection
to weight zero at their product gives a retraction onto the regular
functions on each moving pivot intersection.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option maxRecDepth 2500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceMarkedFaceProjection

open AlgebraicGeometry CategoryTheory TopologicalSpace
  CycleQ2IncidenceMarkedPivotFaces CycleQ2CartierProjectiveCover CycleQ2CartierSurfaceGrading
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionProjection
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralNativeCartierFrames
  CycleQ2LiteralMovingDivisorChern CycleQ2IncidenceMarkedProjectorCharts

private abbrev X := projectiveSurface 57 1

theorem vertices_nonempty {S : Face} (hS : S.Nonempty) : (vertices S).Nonempty := hS.image _

theorem vertex_mem {S : Face} {a : VertexIndex} (h : a ∈ S) : a.1 ∈ vertices S :=
  Finset.mem_image_of_mem _ h

def entry (S : Face) (hS : S.Nonempty) (a : VertexIndex) : ClosedRing (vertices S) :=
  if h : a.1 ∈ vertices S then CycleQ2LiteralMovingPivotPrincipal.pivotEntry (vertices S) (vertices_nonempty hS) a h else 1

theorem entry_eq {S : Face} (hS : S.Nonempty) {a : VertexIndex} (ha : a ∈ S) :
    entry S hS a = CycleQ2LiteralMovingPivotPrincipal.pivotEntry (vertices S) (vertices_nonempty hS) a (vertex_mem ha) :=
  dif_pos (vertex_mem ha)

def normalizedProduct (S : Face) (hS : S.Nonempty) := ∏ a ∈ S, entry S hS a

theorem entry_associated {S : Face} (hS : S.Nonempty) {a : VertexIndex} (ha : a ∈ S) :
    Associated ((entry S hS a).val) (ordinaryReduction (vertices S) (polynomialPivot (vertices S) (seedPivot a))) := by
  let t := vertices S
  have hv := vertex_mem ha
  have hu := (closedCoordinateValue_isUnit t a.1 hv).pow 14
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec, entry_eq hS ha, CycleQ2IncidenceMarkedNativeCharts.pivotEntry_eq_normalized]
  exact (reduction_normalized_mul t a.1 hv _ _).trans
    (ordinaryReduction_base t _).symm

theorem product_associated (S : Face) (hS : S.Nonempty) :
    Associated (algebraMap (ClosedRing (vertices S)) (ClosedCone (vertices S)) (normalizedProduct S hS))
      (ordinaryReduction (vertices S) (pivotDen S)) := by
  simp only [normalizedProduct, pivotDen, pivotProduct, map_prod]
  exact Associated.prod S _ _ (fun a ha => entry_associated hS ha)

instance face_localizes (S : Face) (hS : S.Nonempty) :
    IsLocalization.Away (algebraMap (ClosedRing (vertices S)) (ClosedCone (vertices S)) (normalizedProduct S hS)) (faceClosed S) :=
  IsLocalization.Away.of_associated (product_associated S hS).symm

def closedProjectionLinear (t : Finset Vertex) : ClosedCone t →ₗ[ClosedRing t] ClosedRing t where
  __ := closedProjection t
  map_smul' a x := CycleQ2GradedLocalizationProjection.degreeZero_mul_homogeneous
    (surfaceGrade 57 1) (closedProduct_homogeneous t) a x

def faceOpen (S : Face) (hS : S.Nonempty) : X.Opens :=
  CycleQ2LiteralMovingPivotPrincipal.principalOpen _ (vertices_nonempty hS) (normalizedProduct S hS)

private theorem principalOpen_prod {ι : Type} (t : Finset Vertex) (ht : t.Nonempty)
    (F : Finset ι) (f : ι → ClosedRing t) :
    CycleQ2LiteralMovingPivotPrincipal.principalOpen t ht (∏ a ∈ F, f a) =
      closedOpen t ⊓ F.inf (fun a => CycleQ2LiteralMovingPivotPrincipal.principalOpen t ht (f a)) := by
  classical
  induction F using Finset.induction_on with
  | empty =>
    simp [CycleQ2LiteralMovingPivotPrincipal.principalOpen, Scheme.basicOpen_one]
  | @insert i F hi ih =>
    rw [Finset.prod_insert hi, Finset.inf_insert]
    rw [show CycleQ2LiteralMovingPivotPrincipal.principalOpen t ht (f i * ∏ a ∈ F, f a) =
          CycleQ2LiteralMovingPivotPrincipal.principalOpen t ht (f i) ⊓
          CycleQ2LiteralMovingPivotPrincipal.principalOpen t ht (∏ a ∈ F, f a) by
      unfold CycleQ2LiteralMovingPivotPrincipal.principalOpen
      rw [map_mul, Scheme.basicOpen_mul], ih]
    ac_rfl

theorem faceOpen_eq (S : Face) (hS : S.Nonempty) : faceOpen S hS = S.inf pivotCover := by
  let t := vertices S
  have hnative : S.inf pivotCover ≤ closedOpen t := by
    rw [closedOpen_eq]
    apply le_iInf
    intro v
    apply le_iInf
    intro hv
    obtain ⟨a,ha,rfl⟩ := Finset.mem_image.mp hv
    exact (Finset.inf_le (f := pivotCover) ha).trans inf_le_left
  have hopen {a : VertexIndex} (ha : a ∈ S) :
      CycleQ2LiteralMovingPivotPrincipal.principalOpen t (vertices_nonempty hS) (entry S hS a) =
        closedOpen t ⊓ CycleQ2SeedSectionInvertible.pivotOpen a.1.2 a.2 := by
    rw [entry_eq hS ha, CycleQ2LiteralMovingPivotPrincipal.pivotEntry_open]
  rw [faceOpen, normalizedProduct, principalOpen_prod]
  apply le_antisymm
  · apply Finset.le_inf
    intro a ha
    apply le_inf
    · exact inf_le_left.trans (CycleQ2LiteralMovingPivotPrincipal.within_vertex t a.1 (vertex_mem ha))
    · exact (inf_le_right.trans (Finset.inf_le ha)).trans ((hopen ha).le.trans inf_le_right)
  · exact le_inf hnative (Finset.le_inf fun a ha => (le_inf hnative ((Finset.inf_le (f := pivotCover) ha).trans inf_le_right)).trans (hopen ha).ge)

theorem faceOpen_mono {S T : Face} (hST : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty) :
    faceOpen T hT ≤ faceOpen S hS := by
  rw [faceOpen_eq, faceOpen_eq]
  exact Finset.le_inf fun _ ha => Finset.inf_le (hST ha)

def principalEquiv (S : Face) (hS : S.Nonempty) :
    Localization.Away (normalizedProduct S hS) ≃+* Γ(X,faceOpen S hS) :=
  CycleQ2LiteralMovingPivotPrincipal.closedPrincipalEquiv (vertices S) (vertices_nonempty hS) (normalizedProduct S hS)

def faceProjection (S : Face) (hS : S.Nonempty) :
    faceClosed S →+ Γ(X,faceOpen S hS) :=
  (principalEquiv S hS).toRingHom.toAddMonoidHom.comp
    (CycleQ2PrincipalProjectionLocalization.projection (L := faceClosed S)
      (normalizedProduct S hS) (closedProjectionLinear (vertices S))).toAddMonoidHom

def nativeSection (S : Face) (hS : S.Nonempty) : ClosedRing (vertices S) →+* Γ(X,faceOpen S hS) :=
  (principalEquiv S hS).toRingHom.comp (algebraMap _ _)

theorem faceProjection_base (S : Face) (hS : S.Nonempty) (x : ClosedCone (vertices S)) :
    faceProjection S hS (toClosed S x) = nativeSection S hS (closedProjection (vertices S) x) :=
  congrArg (principalEquiv S hS) (CycleQ2PrincipalProjectionLocalization.projection_base
    (L := faceClosed S) (normalizedProduct S hS) (closedProjectionLinear (vertices S)) x)

theorem faceProjection_smul (S : Face) (hS : S.Nonempty) (a : ClosedRing (vertices S)) (x : faceClosed S) :
    faceProjection S hS (a • x) = nativeSection S hS a * faceProjection S hS x := by
  change principalEquiv S hS (CycleQ2PrincipalProjectionLocalization.projection _ _ (a • x)) = _
  rw [map_smul, Algebra.smul_def, map_mul] <;> rfl

private theorem face_smul (S : Face) (a : ClosedRing (vertices S)) (z : faceClosed S) :
    a • z = toClosed S a.val * z := by
  rw [Algebra.smul_def, IsScalarTower.algebraMap_apply (ClosedRing (vertices S)) (ClosedCone (vertices S)) (faceClosed S)] <;> rfl

theorem nativeSection_unit (S : Face) (hS : S.Nonempty) : IsUnit (nativeSection S hS (normalizedProduct S hS)) :=
  (IsLocalization.Away.algebraMap_isUnit (normalizedProduct S hS)).map (principalEquiv S hS).toRingHom

private def locToFace (S : Face) (hS : S.Nonempty) : Localization.Away (normalizedProduct S hS) →+* faceClosed S :=
  IsLocalization.Away.lift (normalizedProduct S hS) (g := (toClosed S).comp (algebraMap _ _))
    (IsLocalization.Away.algebraMap_isUnit (S := faceClosed S) _)

def nativeToFace (S : Face) (hS : S.Nonempty) : Γ(X,faceOpen S hS) →+* faceClosed S :=
  (locToFace S hS).comp (principalEquiv S hS).symm.toRingHom

theorem faceProjection_native (S : Face) (hS : S.Nonempty) (z : Γ(X,faceOpen S hS)) :
    faceProjection S hS (nativeToFace S hS z) = z := by
  obtain ⟨x,rfl⟩ := (principalEquiv S hS).surjective z
  change faceProjection S hS (locToFace S hS ((principalEquiv S hS).symm (principalEquiv S hS x))) = _
  rw [RingEquiv.symm_apply_apply]
  let p := normalizedProduct S hS
  let A := ClosedRing (vertices S)
  have hbase (a : A) : locToFace S hS (algebraMap A (Localization.Away p) a) = toClosed S a.val :=
    IsLocalization.Away.lift_eq _ _ a
  apply CycleQ2PrincipalProjectionLocalization.ext_of_scalar p (Algebra.linearMap A (Localization.Away p))
    (fun y => faceProjection S hS (locToFace S hS y)) (principalEquiv S hS)
    (nativeSection S hS) (nativeSection_unit S hS)
  · intro a y
    rw [Algebra.smul_def, map_mul, hbase, ← face_smul]
    exact faceProjection_smul S hS a _
  · intro a y
    rw [Algebra.smul_def, map_mul]
    rfl
  · intro a
    change faceProjection S hS (locToFace S hS (algebraMap A (Localization.Away p) a)) = _
    rw [hbase, faceProjection_base, closedProjection_val]
    rfl

def sectionRestrict {S T : Face} (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty) :
    Γ(X,faceOpen S hS) →+* Γ(X,faceOpen T hT) :=
  (X.presheaf.map (homOfLE (faceOpen_mono h hS hT)).op).hom

theorem nativeSection_restrict {S T : Face} (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
    (a : ClosedRing (vertices S)) :
    sectionRestrict h hS hT (nativeSection S hS a) =
      nativeSection T hT (closedRestriction (vertices_mono h) a) := by
  change X.presheaf.map (homOfLE (faceOpen_mono h hS hT)).op
    (CycleQ2LiteralMovingPivotPrincipal.closedPrincipalEquiv _ _ _ (algebraMap _ _ a)) =
      CycleQ2LiteralMovingPivotPrincipal.closedPrincipalEquiv _ _ _ (algebraMap _ _ (closedRestriction _ a))
  rw [CycleQ2LiteralMovingPivotPrincipal.closedPrincipalEquiv_base,
    CycleQ2LiteralMovingPivotPrincipal.closedPrincipalEquiv_base,
    ← closedSectionsEquiv_restrict (vertices_nonempty hS) (vertices_nonempty hT) (vertices_mono h)]
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp] <;> rfl

theorem nativeToFace_base (S : Face) (hS : S.Nonempty) (a : ClosedRing (vertices S)) :
    nativeToFace S hS (nativeSection S hS a) = toClosed S a.val := by
  change locToFace S hS ((principalEquiv S hS).symm (principalEquiv S hS (algebraMap _ _ a))) = _
  rw [RingEquiv.symm_apply_apply]
  exact IsLocalization.Away.lift_eq _ _ a

theorem nativeToFace_restrict {S T : Face} (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
    (z : Γ(X,faceOpen S hS)) :
    faceClosedRestrict h (nativeToFace S hS z) = nativeToFace T hT (sectionRestrict h hS hT z) := by
  obtain ⟨y,rfl⟩ := (principalEquiv S hS).surjective z
  have he : ((faceClosedRestrict h).comp (nativeToFace S hS)).comp (principalEquiv S hS).toRingHom =
      ((nativeToFace T hT).comp (sectionRestrict h hS hT)).comp (principalEquiv S hS).toRingHom := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (normalizedProduct S hS))
    apply RingHom.ext
    intro a
    change faceClosedRestrict h (nativeToFace S hS (nativeSection S hS a)) =
      nativeToFace T hT (sectionRestrict h hS hT (nativeSection S hS a))
    rw [nativeToFace_base, nativeSection_restrict, nativeToFace_base, faceClosedRestrict_base, closedRestriction_val]
  exact RingHom.congr_fun he y

theorem faceProjection_restrict {S T : Face} (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
    (x : faceClosed S) :
    sectionRestrict h hS hT (faceProjection S hS x) = faceProjection T hT (faceClosedRestrict h x) := by
  let A := ClosedRing (vertices S)
  let B := ClosedCone (vertices S)
  let L := faceClosed S
  let p := normalizedProduct S hS
  let j := (IsScalarTower.toAlgHom A B L).toLinearMap
  letI : IsLocalizedModule (Submonoid.powers p) j :=
    CycleQ2PrincipalProjectionLocalization.base_localizes (B := B) (L := L) p
  let c := (sectionRestrict h hS hT).comp (nativeSection S hS)
  apply CycleQ2PrincipalProjectionLocalization.ext_of_scalar p j
    (fun z => sectionRestrict h hS hT (faceProjection S hS z))
    (fun z => faceProjection T hT (faceClosedRestrict h z)) c
    ((nativeSection_unit S hS).map (sectionRestrict h hS hT))
  · intro a z
    rw [faceProjection_smul, map_mul]
    rfl
  · intro a z
    have hr : faceClosedRestrict h (a • z) = closedRestriction (vertices_mono h) a • faceClosedRestrict h z := by
      rw [face_smul, face_smul, map_mul, faceClosedRestrict_base, closedRestriction_val]
    rw [hr, faceProjection_smul, ← nativeSection_restrict h hS hT]
    rfl
  · intro b
    change sectionRestrict h hS hT (faceProjection S hS (toClosed S b)) =
      faceProjection T hT (faceClosedRestrict h (toClosed S b))
    rw [faceClosedRestrict_base, faceProjection_base, faceProjection_base,
      closedProjection_restrict, nativeSection_restrict]

section NativePrincipalCharts

open CycleQ2GeometricKernelLocalization CycleQ2IncidenceMarkedNativeCharts
attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra

theorem normalizedProduct_isUnit (S : Face) (hS : S.Nonempty) :
    IsUnit (closedBase _ (pivotDen S) (normalizedProduct S hS)) := by
  change IsUnit (algebraMap (ClosedCone (vertices S)) (faceClosed S)
    (algebraMap (ClosedRing (vertices S)) (ClosedCone (vertices S)) (normalizedProduct S hS)))
  exact IsLocalization.Away.algebraMap_isUnit _

theorem nativeLift_isUnit (S : Face) (hS : S.Nonempty) (p : ThickRing (vertices S))
    (hp : nativeReduction _ p = normalizedProduct S hS) :
    IsUnit (closedBase _ (pivotDen S) (nativeReduction _ p)) := by
  rw [hp]
  exact normalizedProduct_isUnit S hS

/-- Restricting a native thick function along the finite face diagram agrees
with its genuine native principal restriction whenever the latter extends
the restriction on the affine vertex intersection. -/
theorem nativeThickMap_restrict {S T : Face} (h : S ⊆ T)
    (p : ThickRing (vertices S)) (q : ThickRing (vertices T))
    (hp : IsUnit (closedBase _ (pivotDen S) (nativeReduction _ p)))
    (hq : IsUnit (closedBase _ (pivotDen T) (nativeReduction _ q)))
    (r : ThickAt (ThickRing (vertices S)) p →+* ThickAt (ThickRing (vertices T)) q)
    (hr : ∀ a : ThickRing (vertices S), r (algebraMap _ _ a) = algebraMap _ _ (thickRestriction (vertices_mono h) a))
    (x : ThickAt (ThickRing (vertices S)) p) :
    faceThickRestrict h (nativeThickMap _ (pivotDen S) p hp x) =
      nativeThickMap _ (pivotDen T) q hq (r x) := by
  have he : (faceThickRestrict h).comp (nativeThickMap _ (pivotDen S) p hp) =
      (nativeThickMap _ (pivotDen T) q hq).comp r := by
    apply IsLocalization.ringHom_ext (Submonoid.powers p)
    apply RingHom.ext
    intro a
    change faceThickRestrict h (nativeThickMap _ _ _ hp (algebraMap _ _ a)) =
      nativeThickMap _ _ _ hq (r (algebraMap _ _ a))
    rw [hr, nativeThickMap_base, nativeThickMap_base]
    exact (faceThickRestrict_base h a.val).trans (congrArg (toThick T) (thickRestriction_val (vertices_mono h) a).symm)
  exact RingHom.congr_fun he x

/-- This also identifies the map from any chosen native presentation of the
same open with the intrinsic inclusion of its sheaf sections in the cone. -/
theorem nativeClosedMap_section (S : Face) (hS : S.Nonempty)
    (p : ThickRing (vertices S)) (hp : IsUnit (closedBase _ (pivotDen S) (nativeReduction _ p)))
    (f : ClosedAt (ThickRing (vertices S)) (ClosedRing (vertices S)) p →+* Γ(X,faceOpen S hS))
    (hf : ∀ a : ClosedRing (vertices S), f (algebraMap _ _ a) = nativeSection S hS a)
    (x : ClosedAt (ThickRing (vertices S)) (ClosedRing (vertices S)) p) :
    nativeClosedMap _ (pivotDen S) p hp x = nativeToFace S hS (f x) := by
  have he : nativeClosedMap _ (pivotDen S) p hp = (nativeToFace S hS).comp f := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (nativeReduction _ p))
    apply RingHom.ext
    intro a
    change nativeClosedMap _ (pivotDen S) p hp (algebraMap _ _ a) =
      nativeToFace S hS (f (algebraMap _ _ a))
    rw [nativeClosedMap_base, hf, nativeToFace_base]
    rfl
  exact RingHom.congr_fun he x

end NativePrincipalCharts

end CycleQ2IncidenceMarkedFaceProjection
end

#print axioms CycleQ2IncidenceMarkedFaceProjection.faceOpen_eq
#print axioms CycleQ2IncidenceMarkedFaceProjection.faceProjection_native

#print axioms CycleQ2IncidenceMarkedFaceProjection.faceProjection_restrict
