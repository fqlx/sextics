import Proposal.GeometricCartierDerivedClass
import Proposal.GeometricResidueDerivedEdge
import Proposal.GeometricLiteralResidueLocalImage

/-! A zero derived cochain represented on an open is a boundary on neighborhoods. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2.NeighborhoodPrimitive
open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite HomologicalComplex
open CycleQ2InjectiveCech (AbSheaf freeOpen freeOpenSections)
open CycleQ2CechTwoToDerived (freeOpenSections_postcomp)
open CycleQ2GeometricResidueDerivedEdge

variable {X : TopCat.{0}}

/-- Sections of the sheaf image admit preimages locally at every specified point. -/
theorem localBoundary {F G : AbSheaf X} (d : F ⟶ G) (U : Opens X)
    (a : G.obj.obj (op U)) (ha : (cokernel.π d).hom.app (op U) a = 0) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (h : V ≤ U), x ∈ V ∧
      ∃ η : F.obj.obj (op V), d.hom.app (op V) η = G.obj.map (homOfLE h).op a := by
  let q := cokernel.π d
  let S := ShortComplex.mk (kernel.ι q) q (kernel.condition q)
  let E := sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat ⋙
    (evaluation _ AddCommGrpCat).obj (op U)
  have hS : S.Exact := ShortComplex.exact_kernel q
  have hES := hS.map_of_mono_of_preservesKernel E
    (inferInstanceAs (Mono (kernel.ι q))) (by infer_instance)
  obtain ⟨v, hv⟩ := (ShortComplex.ab_exact_iff (S.map E)).mp hES a ha
  change (kernel.ι q).hom.app (op U) v = a at hv
  let l := kernel.lift q d (cokernel.condition d)
  have : Epi l := (ShortComplex.exact_cokernel d).epi_kernelLift
  have : Sheaf.IsLocallySurjective l :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat l).mpr inferInstance
  obtain ⟨V, i, ⟨η, hη⟩, hxV⟩ :=
    Presheaf.imageSieve_mem (Opens.grothendieckTopology X) l.hom v x hx
  refine ⟨V, leOfHom i, hxV, η, ?_⟩
  have hl : l ≫ kernel.ι q = d := kernel.lift_ι _ _ _
  calc
    d.hom.app (op V) η = (kernel.ι q).hom.app (op V) (l.hom.app (op V) η) :=
      congrArg (fun k : F ⟶ G => k.hom.app (op V) η) hl.symm
    _ = _ := by rw [hη, NatTrans.naturality_apply, hv]

variable [HasDerivedCategory (AbSheaf X)]

/-- Zero of a derived class on an open gives its actual local primitives. The
incoming differential can have a nonzero target differential. -/
theorem of_derived_zero (K : CochainComplex (AbSheaf X) ℤ) (n : ℤ) (U : Opens X)
    (c : (single (AbSheaf X) (ComplexShape.up ℤ) n).obj (freeOpen U) ⟶ K)
    (h : DerivedCategory.Q.map c = 0) (x : X) (hx : x ∈ U) :
    ∃ (V : Opens X) (hV : V ≤ U), x ∈ V ∧
      ∃ η : (K.X (n-1)).obj.obj (op V), (K.d (n-1) n).hom.app (op V) η =
        (K.X n).obj.map (homOfLE hV).op
          (freeOpenSections (K.X n) U
            ((singleObjXSelf (ComplexShape.up ℤ) n (freeOpen U)).inv ≫ c.f n)) := by
  let α := (singleObjXSelf (ComplexShape.up ℤ) n (freeOpen U)).inv ≫ c.f n
  have hc (j : ℤ) (_ : (ComplexShape.up ℤ).Rel n j) : α ≫ K.d n j = 0 := by
    simp [α, Category.assoc, c.comm]
  have hmk : mkHomFromSingle α hc = c := by
    apply from_single_hom_ext
    simp [α, mkHomFromSingle_f]
  have hq := comp_cokernel_eq_zero_of_derived_zero K n α hc (by rwa [hmk])
  let q := cokernel.π (K.d (n-1) n)
  have hqa := congrArg (freeOpenSections (cokernel (K.d (n-1) n)) U) hq
  rw [map_zero] at hqa
  refine localBoundary (K.d (n-1) n) U _ ?_ x hx
  exact (freeOpenSections_postcomp U α q).trans hqa

/-- The actual section on an open corresponding to a map out of the free-open
complex concentrated in degree n. -/
abbrev sectionOf (K : CochainComplex (AbSheaf X) ℤ) (n : ℤ) (U : Opens X)
    (c : (single (AbSheaf X) (ComplexShape.up ℤ) n).obj (freeOpen U) ⟶ K) :=
  freeOpenSections (K.X n) U ((singleObjXSelf (ComplexShape.up ℤ) n (freeOpen U)).inv ≫ c.f n)

theorem sectionOf_restrict (K : CochainComplex (AbSheaf X) ℤ) (n : ℤ) {V U : Opens X}
    (h : V ≤ U) (c : (single (AbSheaf X) (ComplexShape.up ℤ) n).obj (freeOpen U) ⟶ K) :
    sectionOf K n V ((single (AbSheaf X) (ComplexShape.up ℤ) n).map
        (CycleQ2InjectiveCech.freeOpenMap h) ≫ c) =
      (K.X n).obj.map (homOfLE h).op (sectionOf K n U c) := by
  simpa only [sectionOf, HomologicalComplex.comp_f, single_map_f_self, Category.assoc,
    Iso.inv_hom_id_assoc] using CycleQ2InjectiveCech.freeOpenSections_naturality (K.X n) h
      ((singleObjXSelf (ComplexShape.up ℤ) n (freeOpen U)).inv ≫ c.f n)

/-- Any additive sheaf morphism which kills exact sections must kill a
section whose map from the open vanishes in the derived category. -/
theorem annihilator_of_derived_zero (K : CochainComplex (AbSheaf X) ℤ) (n : ℤ) (U : Opens X)
    (c : (single (AbSheaf X) (ComplexShape.up ℤ) n).obj (freeOpen U) ⟶ K)
    (hz : DerivedCategory.Q.map c = 0) {N : AbSheaf X} (e : K.X n ⟶ N)
    (he : K.d (n-1) n ≫ e = 0) : e.hom.app (op U) (sectionOf K n U c) = 0 := by
  apply TopCat.Presheaf.IsSheaf.section_ext N.property
  intro x hx
  obtain ⟨V, hV, hxV, η, hη⟩ := of_derived_zero K n U c hz x hx
  refine ⟨V, hV, hxV, ?_⟩
  change N.obj.map (homOfLE hV).op (e.hom.app (op U) _) = N.obj.map (homOfLE hV).op 0
  rw [← NatTrans.naturality_apply, ← hη, map_zero]
  exact congrArg (fun f : K.X (n-1) ⟶ N ↦ f.hom.app (op V) η) he

end CycleQ2.NeighborhoodPrimitive
end
#print axioms CycleQ2.NeighborhoodPrimitive.of_derived_zero
