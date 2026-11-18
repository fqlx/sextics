import Proposal.GeometricLiteralAbelJacobiMovingFaces
import Proposal.GeometricLiteralCotangentRestriction
import Proposal.GeometricChartSectionPullback

/-!
# The principal intersection of the three moving pivots

The denominator on a native triple chart is the product of the three
degree-zero matrix entries in their respective spatial frames.
Its nonvanishing locus is the actual moving Čech triple open.
The principal closed and thick rings are identified with their structure
sheaf sections.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1100000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingPivotPrincipal
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  CycleQ2CartierProjectiveCover CycleQ2CartierSurfaceGrading
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralProjectiveDeformation
  CycleQ2LiteralProjectiveIntersectionKernel CycleQ2LiteralCotangentRestriction
  CycleQ2SeedSectionInvertible CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedSectionDivisorTransitions CycleQ2LiteralMovingDivisorChern

private abbrev X := projectiveSurface 57 1
private abbrev Y := projectiveDeformation

theorem within_vertex (s : Finset Vertex) (a : Vertex) (ha : a ∈ s) :
    closedOpen s ≤ cover a := by
  rw [closedOpen_eq]
  exact iInf_le_of_le a (iInf_le _ ha)

def pivotEntry (s : Finset Vertex) (hs : s.Nonempty) (a : VertexIndex) (ha : a.1 ∈ s) : ClosedRing s :=
  (closedSectionsEquiv s hs).symm
    (sectionMatrix a.1.2 (closedOpen s) ((within_vertex s a.1 ha).trans (cover_le_patch a.1)) a.2.1 a.2.2)

theorem pivotEntry_section (s : Finset Vertex) (hs : s.Nonempty) (a : VertexIndex) (ha : a.1 ∈ s) :
    closedSectionsEquiv s hs (pivotEntry s hs a ha) =
      sectionMatrix a.1.2 (closedOpen s) ((within_vertex s a.1 ha).trans (cover_le_patch a.1)) a.2.1 a.2.2 :=
  (closedSectionsEquiv s hs).apply_symm_apply _

theorem pivotEntry_polynomial (s : Finset Vertex) (hs : s.Nonempty) (a : VertexIndex) (ha : a.1 ∈ s) :
    closedSectionsEquiv s hs (pivotEntry s hs a ha) =
      polynomialSection a.1.2 (closedOpen s) ((within_vertex s a.1 ha).trans (cover_le_patch a.1))
        (CycleQ2IncidenceEquations.rawSeedMatrix (57 : ℂ) a.2.1 a.2.2) := by
  rw [pivotEntry_section, sectionMatrix_entry]

def principalOpen (s : Finset Vertex) (hs : s.Nonempty) (q : ClosedRing s) : X.Opens :=
  X.basicOpen (closedSectionsEquiv s hs q)

def thickPrincipalOpen (s : Finset Vertex) (hs : s.Nonempty) (q : ThickRing s) : Y.Opens :=
  Y.basicOpen (thickSectionsEquiv s hs q)

theorem principalOpen_le (s : Finset Vertex) (hs : s.Nonempty) (q : ClosedRing s) :
    principalOpen s hs q ≤ closedOpen s := X.basicOpen_le _

theorem pivotEntry_open (s : Finset Vertex) (hs : s.Nonempty) (a : VertexIndex) (ha : a.1 ∈ s) :
    principalOpen s hs (pivotEntry s hs a ha) = closedOpen s ⊓ pivotOpen a.1.2 a.2 := by
  unfold principalOpen pivotOpen
  rw [pivotEntry_section]
  let h := (within_vertex s a.1 ha).trans (cover_le_patch a.1)
  rw [← sectionMatrix_restrict a.1.2 h le_rfl a.2.1 a.2.2]
  exact X.basicOpen_res _ (homOfLE h).op

abbrev vertices (a b c : VertexIndex) : Finset Vertex := {a.1,b.1,c.1}
abbrev inhabitedVertices (a b c : VertexIndex) : (vertices a b c).Nonempty := ⟨a.1,by simp [vertices]⟩
abbrev face (a b c : VertexIndex) := (pivotCover a ⊓ pivotCover b) ⊓ pivotCover c

def pivotProduct (a b c : VertexIndex) : ClosedRing (vertices a b c) :=
  pivotEntry _ (inhabitedVertices a b c) a (by simp [vertices]) *
  pivotEntry _ (inhabitedVertices a b c) b (by simp [vertices]) *
  pivotEntry _ (inhabitedVertices a b c) c (by simp [vertices])

private theorem inf_triplet {L : Type*} [SemilatticeInf L] (i j k x y z : L) :
    (((i⊓j)⊓k)⊓x) ⊓ (((i⊓j)⊓k)⊓y) ⊓ (((i⊓j)⊓k)⊓z) = ((i⊓x)⊓(j⊓y))⊓(k⊓z) := by
  simp only [inf_assoc, inf_left_comm, inf_comm, inf_idem, inf_left_idem]

private theorem principalOpen_mul (s : Finset Vertex) (hs : s.Nonempty) (x y : ClosedRing s) :
    principalOpen s hs (x*y) = principalOpen s hs x ⊓ principalOpen s hs y := by
  unfold principalOpen
  rw [map_mul, Scheme.basicOpen_mul]

set_option maxHeartbeats 1800000 in
theorem pivotProduct_open (a b c : VertexIndex) :
    principalOpen _ (inhabitedVertices a b c) (pivotProduct a b c) = face a b c := by
  let s := vertices a b c
  let hs := inhabitedVertices a b c
  have hnative : closedOpen s = (cover a.1 ⊓ cover b.1) ⊓ cover c.1 :=
    le_antisymm (le_inf (le_inf (within_vertex s a.1 (by simp [s,vertices]))
      (within_vertex s b.1 (by simp [s,vertices]))) (within_vertex s c.1 (by simp [s,vertices])))
      (CycleQ2LiteralNativeCupSectionValues.common_le_triple a.1 b.1 c.1 _ (inf_le_left.trans inf_le_left)
        (inf_le_left.trans inf_le_right) inf_le_right)
  unfold pivotProduct
  rw [principalOpen_mul, principalOpen_mul, pivotEntry_open, pivotEntry_open, pivotEntry_open, hnative]
  exact inf_triplet _ _ _ _ _ _

/-- Structure sheaf sections on a principal open in a specified affine chart. -/
def chartPrincipalEquiv {S : Scheme.{0}} {A : Type} [CommRing A]
    (U : S.Opens) (hU : IsAffineOpen U) (e : A ≃+* Γ(S,U)) (q : A) :
    Localization.Away q ≃+* Γ(S,S.basicOpen (e q)) := by
  let h := S.basicOpen_le (e q)
  letI : Algebra Γ(S,U) Γ(S,S.basicOpen (e q)) := (S.presheaf.map (homOfLE h).op).hom.toAlgebra
  letI : IsLocalization.Away (e q) Γ(S,S.basicOpen (e q)) := hU.isLocalization_of_eq_basicOpen (e q) (homOfLE h) rfl
  exact IsLocalization.ringEquivOfRingEquiv (M := Submonoid.powers q) (T := Submonoid.powers (e q)) (Localization.Away q) Γ(S,S.basicOpen (e q)) e (Submonoid.map_powers e.toMonoidHom q)

theorem chartPrincipalEquiv_base {S : Scheme.{0}} {A : Type} [CommRing A]
    (U : S.Opens) (hU : IsAffineOpen U) (e : A ≃+* Γ(S,U)) (q x : A) :
    chartPrincipalEquiv U hU e q (algebraMap A (Localization.Away q) x) =
      S.presheaf.map (homOfLE (S.basicOpen_le (e q))).op (e x) := by
  let h := S.basicOpen_le (e q)
  let : Algebra Γ(S,U) Γ(S,S.basicOpen (e q)) := (S.presheaf.map (homOfLE h).op).hom.toAlgebra
  let : IsLocalization.Away (e q) Γ(S,S.basicOpen (e q)) := hU.isLocalization_of_eq_basicOpen (e q) (homOfLE h) rfl
  exact IsLocalization.ringEquivOfRingEquiv_eq (M := Submonoid.powers q) (T := Submonoid.powers (e q))
    (S := Localization.Away q) (Q := Γ(S,S.basicOpen (e q))) (j := e) (Submonoid.map_powers e.toMonoidHom q) x

def closedPrincipalEquiv (s : Finset Vertex) (hs : s.Nonempty) (q : ClosedRing s) :
    Localization.Away q ≃+* Γ(X,principalOpen s hs q) :=
  chartPrincipalEquiv (closedOpen s)
    (Proj.isAffineOpen_basicOpen (surfaceGrade 57 1) (closedProduct s) (closedProduct_homogeneous s) (productDegree_pos hs))
    (closedSectionsEquiv s hs) q

theorem closedPrincipalEquiv_base (s : Finset Vertex) (hs : s.Nonempty) (q x : ClosedRing s) :
    closedPrincipalEquiv s hs q (algebraMap (ClosedRing s) (Localization.Away q) x) =
      X.presheaf.map (homOfLE (principalOpen_le s hs q)).op (closedSectionsEquiv s hs x) :=
  chartPrincipalEquiv_base (closedOpen s) _ (closedSectionsEquiv s hs) q x

def thickPrincipalEquiv (s : Finset Vertex) (hs : s.Nonempty) (q : ThickRing s) :
    Localization.Away q ≃+* Γ(Y,thickPrincipalOpen s hs q) :=
  chartPrincipalEquiv (thickOpen s)
    (Proj.isAffineOpen_basicOpen _ (thickProduct s) (thickProduct_homogeneous s) (productDegree_pos hs))
    (thickSectionsEquiv s hs) q

theorem thickPrincipalEquiv_base (s : Finset Vertex) (hs : s.Nonempty) (p x : ThickRing s) :
    thickPrincipalEquiv s hs p (algebraMap (ThickRing s) (Localization.Away p) x) =
      Y.presheaf.map (homOfLE (Y.basicOpen_le (thickSectionsEquiv s hs p))).op (thickSectionsEquiv s hs x) :=
  chartPrincipalEquiv_base (thickOpen s) _ (thickSectionsEquiv s hs) p x

theorem preimage_thickPrincipal (s : Finset Vertex) (hs : s.Nonempty) (p : ThickRing s) :
    closedFiber ⁻¹ᵁ thickPrincipalOpen s hs p = principalOpen s hs (nativeReduction s p) := by
  unfold thickPrincipalOpen principalOpen
  rw [Scheme.preimage_basicOpen, ← nativeReduction_section]
  exact (X.basicOpen_res_eq _ (eqToHom (closedFiber_preimage_thickOpen s).symm).op).symm

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra

/-- Reduction on the localized native ring is the true morphism of
structure sheaves of the ambient-test thickening on this same open. -/
theorem principalReduction_section (s : Finset Vertex) (hs : s.Nonempty) (p : ThickRing s)
    (x : Localization.Away p) :
    closedFiber.appLE (thickPrincipalOpen s hs p) (principalOpen s hs (nativeReduction s p))
      (preimage_thickPrincipal s hs p).ge (thickPrincipalEquiv s hs p x) =
      closedPrincipalEquiv s hs (nativeReduction s p)
        (CycleQ2GeometricKernelLocalization.localReduction (ThickRing s) (ClosedRing s) p x) := by
  let U := thickPrincipalOpen s hs p
  let V := principalOpen s hs (nativeReduction s p)
  let H := CycleQ2GeometricKernelLocalization.localReduction (ThickRing s) (ClosedRing s) p
  have he : (closedFiber.appLE U V (preimage_thickPrincipal s hs p).ge).hom.comp (thickPrincipalEquiv s hs p).toRingHom =
      (closedPrincipalEquiv s hs (nativeReduction s p)).toRingHom.comp H := by
    apply IsLocalization.ringHom_ext (Submonoid.powers p)
    apply RingHom.ext
    intro z
    change closedFiber.appLE U V _ (thickPrincipalEquiv s hs p (algebraMap (ThickRing s) (Localization.Away p) z)) =
      closedPrincipalEquiv s hs (nativeReduction s p) (CycleQ2GeometricKernelLocalization.localReduction _ _ p (algebraMap _ _ z))
    rw [thickPrincipalEquiv_base, CycleQ2GeometricKernelLocalization.localReduction_base]
    refine Eq.trans ?_ (closedPrincipalEquiv_base s hs (nativeReduction s p) (nativeReduction s z)).symm
    exact (CycleQ2ChartSectionPullback.restriction_square closedFiber (Y.basicOpen_le (thickSectionsEquiv s hs p))
      (closedFiber_preimage_thickOpen s).ge (principalOpen_le s hs _) (preimage_thickPrincipal s hs p).ge
      (thickSectionsEquiv s hs z)).trans
      (congrArg (X.presheaf.map (homOfLE (principalOpen_le s hs _)).op) (nativeReduction_section s hs z))
  exact RingHom.congr_fun he x

end CycleQ2LiteralMovingPivotPrincipal
end

#print axioms CycleQ2LiteralMovingPivotPrincipal.pivotProduct_open
#print axioms CycleQ2LiteralMovingPivotPrincipal.closedPrincipalEquiv
#print axioms CycleQ2LiteralMovingPivotPrincipal.thickPrincipalEquiv

#print axioms CycleQ2LiteralMovingPivotPrincipal.principalReduction_section
