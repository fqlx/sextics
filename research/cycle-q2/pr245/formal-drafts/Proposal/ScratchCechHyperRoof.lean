import Mathlib.Algebra.Homology.DerivedCategory.Basic
import Mathlib.Algebra.Homology.Embedding.ExtendHomology

/-!
# Derived class of a cocycle on an augmented Čech resolution

Put the chart-chain degree p at cochain degree n−p. A comparison map from
the reindexed resolution to a complex K determines a derived cohomology class
with constant source in degree n. Restriction at a vertex is represented by
the literal degree-zero component of the Čech cocycle.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2.CechHyperRoof

open CategoryTheory CategoryTheory.Limits HomologicalComplex

universe u v w
variable {C : Type u} [Category.{v} C] [Abelian C]
variable (n : ℤ) {A B : C} {R : ChainComplex C ℕ} {K : CochainComplex C ℤ}

abbrev reindex := ComplexShape.embeddingUpIntLE

lemma reindex_zero : (reindex n).f 0 = n := by simp [reindex]

/-- Reindex the Čech augmentation so that it terminates at degree n. -/
def augmentation (ε : R ⟶ (ChainComplex.single₀ C).obj A) :
    R.extend (reindex n) ⟶ (single C (ComplexShape.up ℤ) n).obj A :=
  extendMap ε (reindex n) ≫ (extendSingleIso (reindex n) A 0 n (reindex_zero n)).hom

instance (ε : R ⟶ (ChainComplex.single₀ C).obj A) [QuasiIso ε] :
    QuasiIso (augmentation n ε) := by
  unfold augmentation
  infer_instance

/-- The chain map corresponding to a section of the degree-zero chart chains. -/
def vertex (v : B ⟶ R.X 0) :
    (single C (ComplexShape.up ℤ) n).obj B ⟶ R.extend (reindex n) :=
  mkHomFromSingle (v ≫ (R.extendXIso (reindex n) (reindex_zero n)).inv) (by
    intro j hj
    rw [R.extend_d_from_eq_zero (reindex n) n j 0 (reindex_zero n) (by simp)]
    simp)

theorem vertex_augmentation (ε : R ⟶ (ChainComplex.single₀ C).obj A)
    (v : B ⟶ R.X 0) :
    vertex n v ≫ augmentation n ε =
      (single C (ComplexShape.up ℤ) n).map (v ≫ ε.f 0) := by
  apply from_single_hom_ext
  simp only [vertex, augmentation, comp_f, mkHomFromSingle_f, single_map_f_self,
    extendSingleIso_hom_f, extendMap_f ε (reindex n) (reindex_zero n), Category.assoc,
    Iso.inv_hom_id_assoc, ChainComplex.single₀ObjXSelf, Iso.refl_hom, Category.id_comp]

/-- The cocycle carried by a chosen vertex, as a chain map. -/
def vertexCocycle (v : B ⟶ R.X 0) (c : R.extend (reindex n) ⟶ K) :
    (single C (ComplexShape.up ℤ) n).obj B ⟶ K :=
  vertex n v ≫ c

/-- Recover the actual section in degree n of the chosen chart. -/
theorem vertexCocycle_component (v : B ⟶ R.X 0) (c : R.extend (reindex n) ⟶ K) :
    (singleObjXSelf (ComplexShape.up ℤ) n B).inv ≫ (vertexCocycle n v c).f n =
      v ≫ (R.extendXIso (reindex n) (reindex_zero n)).inv ≫ c.f n := by
  simp [vertexCocycle, vertex, Category.assoc]

variable [HasDerivedCategory.{w} C]

/-- The derived roof associated to a Čech cocycle. -/
def hyperClass (ε : R ⟶ (ChainComplex.single₀ C).obj A) [QuasiIso ε]
    (c : R.extend (reindex n) ⟶ K) :
    DerivedCategory.Q.obj ((single C (ComplexShape.up ℤ) n).obj A) ⟶ DerivedCategory.Q.obj K :=
  inv (DerivedCategory.Q.map (augmentation n ε)) ≫ DerivedCategory.Q.map c

theorem hyperClass_homotopy (ε : R ⟶ (ChainComplex.single₀ C).obj A) [QuasiIso ε]
    {c c' : R.extend (reindex n) ⟶ K} (h : Homotopy c c') :
    hyperClass n ε c = hyperClass n ε c' := by
  rw [hyperClass, hyperClass, DerivedCategory.Q_map_eq_of_homotopy h]

/-- Restriction of the roof to a vertex gives its degree-zero Čech component. -/
theorem hyperClass_vertex (ε : R ⟶ (ChainComplex.single₀ C).obj A) [QuasiIso ε]
    (v : B ⟶ R.X 0) (c : R.extend (reindex n) ⟶ K) :
    DerivedCategory.Q.map ((single C (ComplexShape.up ℤ) n).map (v ≫ ε.f 0)) ≫
      hyperClass n ε c = DerivedCategory.Q.map (vertexCocycle n v c) := by
  rw [← vertex_augmentation n ε v]
  simp [hyperClass, vertexCocycle, Functor.map_comp, Category.assoc]

end CycleQ2.CechHyperRoof

#print axioms CycleQ2.CechHyperRoof.hyperClass_vertex
