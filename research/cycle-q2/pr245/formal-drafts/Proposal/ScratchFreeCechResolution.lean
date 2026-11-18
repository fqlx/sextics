import Mathlib.AlgebraicTopology.ExtraDegeneracy
import Mathlib.Algebra.Homology.QuasiIso
import Mathlib.Algebra.Category.Grp.Adjunctions
import Mathlib.Algebra.Category.Grp.Abelian
import Mathlib.Tactic.FinCases
import Mathlib.CategoryTheory.Limits.Types.Limits
import Mathlib.Topology.Sheaves.Sheaf
import Mathlib.Data.Fin.Tuple.Basic

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2.FreeCechResolution
open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology TopologicalSpace
open scoped Simplicial

/-- The Čech nerve of a set of available chart indices over a point. -/
def nerve (S : Type) : SimplicialObject (Type) where
  obj n := Fin (n.unop.len + 1) → S
  map f := ↾fun t ↦ t ∘ f.unop.toOrderHom
  map_id _ := rfl
  map_comp _ _ := rfl

def augmented (S : Type) : SimplicialObject.Augmented (Type) where
  left := nerve S
  right := PUnit
  hom := { app _ := ↾fun _ ↦ PUnit.unit }

def nerveFunctor : Type ⥤ SimplicialObject.Augmented (Type) where
  obj := augmented
  map f :=
    { left := { app _ := ↾fun t ↦ f ∘ t }
      right := 𝟙 _ }
  map_id _ := rfl
  map_comp _ _ := rfl

/-- Choosing a chart gives an actual contracting extra degeneracy, by prepending it. -/
def prepend {S : Type} (s : S) : (augmented S).ExtraDegeneracy where
  s' := ↾fun _ _ ↦ s
  s _ := ↾fun t ↦ Fin.cons s t
  s'_comp_ε := rfl
  s₀_comp_δ₁ := by
    ext t j
    fin_cases j
    rfl
  s_comp_δ₀ n := by
    ext t j
    change Fin.cons s t (Fin.succAbove 0 j) = _
    simp
  s_comp_δ n i := by
    ext t j
    change Fin.cons s t (i.succ.succAbove j) = Fin.cons s (t ∘ i.succAbove) j
    exact congrFun (Fin.cons_comp_succ_succAbove s t i) j
  s_comp_σ n i := by
    ext t j
    change Fin.cons s t (i.succ.predAbove j) = Fin.cons s (t ∘ i.predAbove) j
    cases j using Fin.cases with
    | zero => simp [Fin.predAbove_of_le_castSucc]
    | succ j => simp

def linearNerve : Type ⥤ SimplicialObject.Augmented AddCommGrpCat :=
  nerveFunctor ⋙ (SimplicialObject.Augmented.whiskering _ _).obj AddCommGrpCat.free

def freeAugmentation :
    linearNerve ⋙ SimplicialObject.Augmented.drop ⋙ alternatingFaceMapComplex AddCommGrpCat ⟶
    linearNerve ⋙ SimplicialObject.Augmented.point ⋙ ChainComplex.single₀ AddCommGrpCat :=
  Functor.whiskerLeft linearNerve AlternatingFaceMapComplex.ε

theorem freeAugmentation_quasiIso {S : Type} (s : S) :
    QuasiIso (freeAugmentation.app S) :=
  ((prepend s).map AddCommGrpCat.free).homotopyEquiv.quasiIso_hom

/-- Reassemble a presheaf of chain complexes into a complex of presheaves. -/
def assemble {C : Type*} [Category* C] (P : C ⥤ ChainComplex AddCommGrpCat ℕ) :
    ChainComplex (C ⥤ AddCommGrpCat) ℕ where
  X n := P ⋙ HomologicalComplex.eval _ _ n
  d i j :=
    { app := fun V ↦ (P.obj V).d i j
      naturality := fun _ _ f ↦ (P.map f).comm i j }
  shape i j h := by apply NatTrans.ext; funext V; exact (P.obj V).shape i j h
  d_comp_d' i j k hij hjk := by apply NatTrans.ext; funext V; exact (P.obj V).d_comp_d i j k

def assembleMap {C : Type*} [Category* C] {P Q : C ⥤ ChainComplex AddCommGrpCat ℕ}
    (f : P ⟶ Q) : assemble P ⟶ assemble Q where
  f n := { app := fun V ↦ (f.app V).f n
           naturality := fun _ _ g ↦ HomologicalComplex.congr_hom (f.naturality g) n }
  comm' i j h := by apply NatTrans.ext; funext V; exact (f.app V).comm i j

def indices {X : Type} [TopologicalSpace X] {ι : Type} (U : ι → Opens X) :
    (Opens X)ᵒᵖ ⥤ Type where
  obj V := {i : ι // V.unop ≤ U i}
  map f := ↾fun i ↦ ⟨i.1, (leOfHom f.unop).trans i.2⟩
  map_id _ := rfl
  map_comp _ _ := rfl

def presheafAugmentation {X : Type} [TopologicalSpace X] {ι : Type} (U : ι → Opens X) :=
  assembleMap (Functor.whiskerLeft (indices U) freeAugmentation)

theorem evaluation_quasiIso {X : Type} [TopologicalSpace X] {ι : Type}
    (U : ι → Opens X) (V : Opens X) (i : ι) (h : V ≤ U i) :
    QuasiIso ((((evaluation _ AddCommGrpCat).obj (op V)).mapHomologicalComplex _).map
      (presheafAugmentation U)) :=
  freeAugmentation_quasiIso (S := (indices U).obj (op V)) ⟨i, h⟩

end CycleQ2.FreeCechResolution
