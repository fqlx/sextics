import Proposal.ScratchCechHyperRoof
import Proposal.ScratchSheafCechResolution

/-! The derived class obtained from the Čech resolution restricts to the
literal form on each vertex of the original cover. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2.CechHyperVertex

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology TopologicalSpace
open CycleQ2.FreeCechResolution CycleQ2LocalCechResolution CycleQ2InjectiveCech
open HomologicalComplex
open scoped Simplicial

universe w

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)

private lemma assembleSingle_zero_app {D : Type*} [Category* D]
    (Y : D ⥤ AddCommGrpCat) (V : D) :
    ((assembleSingle Y).hom.f 0).app V = 𝟙 (Y.obj V) := by
  simp [assembleSingle]

lemma presheafAugmentation_zero :
    (presheafAugmentation U).f 0 ≫ (assembleSingle (FreeCech.freeUnitPresheaf X)).hom.f 0 =
    Functor.whiskerRight (FreeCech.toUnit U (Fin 1)) AddCommGrpCat.free := by
  apply NatTrans.ext
  funext V
  rw [NatTrans.comp_app, assembleSingle_zero_app, Category.comp_id] <;>
    (change (AlternatingFaceMapComplex.ε.app (linearNerve.obj ((indices U).obj V))).f 0 = _
     rw [AlternatingFaceMapComplex.ε_app_f_zero] <;> rfl)

/-- Degree zero of the global augmentation forgets the chosen vertex. -/
theorem resolutionAugmentation_zero :
    (resolutionAugmentation U).f 0 =
      FreeCech.augmentation U (Fin 1) ≫ (FreeCech.freeUnitIsoTop (X := X)).hom := by
  simp only [resolutionAugmentation, coverAugmentation, comp_f,
    Functor.mapHomologicalComplex_map_f, Iso.app_hom, singleMapHomologicalComplex_hom_app_self,
    ChainComplex.single₀ObjXSelf, Iso.refl_hom, Iso.refl_inv, Functor.map_id,
    Category.id_comp, ChainComplex.single₀_map_f_zero]
  rw [← Category.assoc, ← Functor.map_comp, presheafAugmentation_zero] <;> rfl

theorem vertex_resolutionAugmentation (i : ι) :
    FreeCech.vertexSheafMap U i ≫ (resolutionAugmentation U).f 0 =
      freeOpenMap (show U i ≤ ⊤ from le_top) := by
  rw [resolutionAugmentation_zero, FreeCech.vertex_augmentation]

variable [HasDerivedCategory.{w} (AbSheaf X)]
variable (n : ℤ) {K : CochainComplex (AbSheaf X) ℤ}

def classOfCover (hc : (⨆ i, U i) = ⊤)
    (c : (coverChains U).extend (CechHyperRoof.reindex n) ⟶ K) :
    DerivedCategory.Q.obj ((single (AbSheaf X) (ComplexShape.up ℤ) n).obj
      (freeOpen (⊤ : Opens X))) ⟶ DerivedCategory.Q.obj K := by
  letI := resolutionAugmentation_quasiIso U hc
  exact CechHyperRoof.hyperClass n (resolutionAugmentation U) c

/-- The restriction of the roof along the actual inclusion of a covering
open is represented by its Čech vertex cocycle. -/
theorem classOfCover_restrict (hc : (⨆ i, U i) = ⊤) (i : ι)
    (c : (coverChains U).extend (CechHyperRoof.reindex n) ⟶ K) :
    DerivedCategory.Q.map ((single (AbSheaf X) (ComplexShape.up ℤ) n).map
      (freeOpenMap (show U i ≤ ⊤ from le_top))) ≫ classOfCover U n hc c =
    DerivedCategory.Q.map (CechHyperRoof.vertexCocycle n (FreeCech.vertexSheafMap U i) c) := by
  letI := resolutionAugmentation_quasiIso U hc
  rw [← vertex_resolutionAugmentation U i]
  exact CechHyperRoof.hyperClass_vertex n _ _ _

/-- The section represented by the restricted cocycle is the component
of the family at the chosen vertex. -/
theorem vertexCocycle_section (i : ι)
    (c : (coverChains U).extend (CechHyperRoof.reindex n) ⟶ K) :
    freeOpenSections (K.X n) (U i)
      ((singleObjXSelf (ComplexShape.up ℤ) n (freeOpen (U i))).inv ≫
        (CechHyperRoof.vertexCocycle n (FreeCech.vertexSheafMap U i) c).f n) =
    (K.X n).obj.map (FreeCech.vertexInclusion U i).op
      (FreeCech.sections U (K.X n) (Fin 1)
        (((coverChains U).extendXIso (CechHyperRoof.reindex n) (CechHyperRoof.reindex_zero n)).inv ≫
          c.f n) (fun _ ↦ i)) := by
  rw [CechHyperRoof.vertexCocycle_component]
  exact FreeCech.vertex_sections U (K.X n) i _

end CycleQ2.CechHyperVertex

#print axioms CycleQ2.CechHyperVertex.classOfCover_restrict
#print axioms CycleQ2.CechHyperVertex.vertexCocycle_section
