import Proposal.ScratchFreeCechResolution
import Proposal.ScratchLocalCechResolution
import Proposal.ScratchFreeCechSections
import Mathlib.Algebra.Homology.DerivedCategory.Basic

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2.FreeCechResolution
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology TopologicalSpace
open CycleQ2LocalCechResolution
open CycleQ2InjectiveCech (AbSheaf freeOpen)
open scoped Simplicial

variable {X : TopCat.{0}} {ι : Type} (U : ι → Opens X)

abbrev coverAugmentation :=
  ((sheafify X).mapHomologicalComplex _).map (presheafAugmentation U)

theorem coverAugmentation_quasiIso (hc : (⨆ i, U i) = ⊤) :
    QuasiIso (coverAugmentation U) :=
  quasiIso_sheafify_of_cover U hc (presheafAugmentation U) fun i V hi ↦
    evaluation_quasiIso U V i hi

abbrev coverChains := ((sheafify X).mapHomologicalComplex _).obj
  (assemble (indices U ⋙ linearNerve ⋙ SimplicialObject.Augmented.drop ⋙
    alternatingFaceMapComplex AddCommGrpCat))

example (n : ℕ) : (coverChains U).X n = FreeCech.freeSheaf U (Fin (n+1)) := rfl

/-- The alternating boundary on chains is the signed sum of the sheafified face maps. -/
theorem coverChains_d (n : ℕ) : (coverChains U).d (n+1) n =
    ∑ i : Fin (n+2), ((-1 : ℤ) ^ i.val) • FreeCech.sheafReindex U i.succAbove := by
  change (sheafify X).map _ = _
  change _ = ∑ i : Fin (n+2), ((-1 : ℤ) ^ i.val) • (sheafify X).map (FreeCech.freeReindex U i.succAbove)
  simp_rw [← Functor.map_zsmul, ← Functor.map_sum]
  congr 1
  apply NatTrans.ext
  funext V
  change (AlternatingFaceMapComplex.obj (linearNerve.obj ((indices U).obj V)).left).d (n+1) n =
    (((evaluation _ AddCommGrpCat).obj V).map _)
  rw [AlternatingFaceMapComplex.obj_d_eq, Functor.map_sum]
  simp_rw [Functor.map_zsmul]
  rfl

/-- On an intersection, the sheaf resolution differential is the usual
alternating sum of the restrictions along its codimension-one faces. -/
theorem sections_coverChains_d (n : ℕ) (G : AbSheaf X) (f : (coverChains U).X n ⟶ G)
    (a : Fin (n+2) → ι) :
    FreeCech.sections U G (Fin (n+2)) ((coverChains U).d (n+1) n ≫ f) a =
      ∑ i : Fin (n+2), ((-1 : ℤ) ^ i.val) •
        G.obj.map (FreeCech.faceInclusion U a i.succAbove).op
          (FreeCech.sections U G (Fin (n+1)) f (a ∘ i.succAbove)) := by
  rw [coverChains_d]
  simp only [Preadditive.sum_comp, Preadditive.zsmul_comp, map_sum, map_zsmul,
    Finset.sum_apply, Pi.smul_apply, FreeCech.sections_reindex]

/-- The assembly of pointwise degree-zero complexes is the degree-zero
presheaf complex. -/
def assembleSingle {C : Type*} [Category* C] (Y : C ⥤ AddCommGrpCat) :
    assemble (Y ⋙ ChainComplex.single₀ AddCommGrpCat) ≅
      (ChainComplex.single₀ (C ⥤ AddCommGrpCat)).obj Y := by
  let zeroAt (i : ℕ) (hi : i ≠ 0) :
      IsZero ((assemble (Y ⋙ ChainComplex.single₀ AddCommGrpCat)).X i) :=
    Functor.isZero _ fun V ↦ HomologicalComplex.isZero_single_obj_X _ 0 (Y.obj V) i hi
  apply HomologicalComplex.Hom.isoOfComponents (fun i ↦ ?_) ?_
  · by_cases hi : i = 0
    · subst i
      exact Functor.isoWhiskerLeft Y (HomologicalComplex.singleCompEvalIsoSelf _ _ 0) ≪≫
        Y.rightUnitor ≪≫ (HomologicalComplex.singleObjXSelf _ 0 Y).symm
    · exact (zeroAt i hi).iso (HomologicalComplex.isZero_single_obj_X _ 0 Y i hi)
  · intro i j h
    apply (zeroAt i (by change j+1=i at h; omega)).eq_of_src

def resolutionAugmentation :
    coverChains U ⟶ (ChainComplex.single₀ (AbSheaf X)).obj (freeOpen (⊤ : Opens X)) :=
  coverAugmentation U ≫
    ((sheafify X).mapHomologicalComplex _).map (assembleSingle (FreeCech.freeUnitPresheaf X)).hom ≫
    ((HomologicalComplex.singleMapHomologicalComplex (sheafify X)
      (ComplexShape.down ℕ) 0).app (FreeCech.freeUnitPresheaf X)).hom ≫
    (ChainComplex.single₀ _).map (FreeCech.freeUnitIsoTop (X := X)).hom

theorem resolutionAugmentation_quasiIso (hc : (⨆ i, U i) = ⊤) :
    QuasiIso (resolutionAugmentation U) := by
  letI := coverAugmentation_quasiIso U hc
  unfold resolutionAugmentation
  infer_instance

end CycleQ2.FreeCechResolution
