import Proposal.ScratchCechComplexEval
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
import Mathlib.CategoryTheory.Limits.Lattice
import Mathlib.AlgebraicGeometry.Morphisms.Affine

/-! The Čech differential evaluated on tuples is the alternating sum of restrictions.
The tuple equivalence also assembles a cochain from sections on each intersection. -/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite
open scoped BigOperators

namespace CycleQ2.Cech

universe w v v' u u'

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
    {ι : Type w} (U : ι → C)

/-- The inclusion into the intersection obtained by omitting entry `j`. -/
noncomputable def faceRestriction {n : ℕ} (x : Fin (n + 2) → ι) (j : Fin (n + 2)) :
    intersection U x ⟶ intersection U (x ∘ j.succAbove) :=
  Pi.lift fun a : Fin (n + 1) => Pi.π (U ∘ x) (j.succAbove a)

/-- Each simplex evaluates the horizontal differential as the signed sum of restrictions. -/
theorem component_d (P : Cᵒᵖ ⥤ A) {n : ℕ} (x : Fin (n + 2) → ι) :
    ((cechComplexFunctor U).obj P).d n (n + 1) ≫ component U P x =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        (component U P (x ∘ j.succAbove) ≫ P.map (faceRestriction U x j).op) := by
  let E := (FormalCoproduct.mk _ U).cech
  let Q := (FormalCoproduct.cosimplicialObjectFunctor E).obj P
  change CochainComplex.of.d (fun n => Q.obj (SimplexCategory.mk n))
    (AlgebraicTopology.AlternatingCofaceMapComplex.objD Q) n (n + 1) ≫ component U P x = _
  rw [CochainComplex.of_d]
  simp only [AlgebraicTopology.AlternatingCofaceMapComplex.objD, Preadditive.sum_comp,
    Preadditive.zsmul_comp]
  apply Finset.sum_congr rfl
  intro j _
  congr 1
  exact Pi.lift_π (fun y : Fin (n + 2) → ι =>
    component U P (y ∘ j.succAbove) ≫ P.map (faceRestriction U y j).op) x

/-- Sections on ordered intersections are precisely cochains for the abelian-group Čech complex. -/
noncomputable def sectionsEquiv (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v'}) (n : ℕ) :
    (((cechComplexFunctor U).obj P).X n : Type (max w v')) ≃
      ∀ x : Fin (n + 1) → ι, P.obj (op (intersection U x)) :=
  Concrete.productEquiv (fun x : Fin (n + 1) → ι => P.obj (op (intersection U x)))

@[simp]
theorem sectionsEquiv_apply (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v'}) {n : ℕ}
    (z : ((cechComplexFunctor U).obj P).X n) (x : Fin (n + 1) → ι) :
    sectionsEquiv U P n z x = component U P x z :=
  Concrete.productEquiv_apply_apply _ z x

@[simp]
theorem component_assemble (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v'}) {n : ℕ}
    (z : ∀ x : Fin (n + 1) → ι, P.obj (op (intersection U x))) (x : Fin (n + 1) → ι) :
    component U P x ((sectionsEquiv U P n).symm z) = z x :=
  Concrete.productEquiv_symm_apply_π _ z x

@[simp]
theorem component_zero (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v'}) {n : ℕ} (x : Fin (n + 1) → ι) :
    component U P x 0 = 0 :=
  map_zero (component U P x).hom

@[simp]
theorem component_add (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v'}) {n : ℕ} (x : Fin (n + 1) → ι)
    (a b : ((cechComplexFunctor U).obj P).X n) :
    component U P x (a + b) = component U P x a + component U P x b :=
  map_add (component U P x).hom a b

@[simp]
theorem component_neg (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v'}) {n : ℕ} (x : Fin (n + 1) → ι)
    (a : ((cechComplexFunctor U).obj P).X n) :
    component U P x (-a) = -(component U P x a) :=
  map_neg (component U P x).hom a

/-- Sections on all simplex intersections determine the cochain. -/
theorem cochain_ext (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v'}) {n : ℕ}
    {a b : ((cechComplexFunctor U).obj P).X n}
    (h : ∀ x : Fin (n + 1) → ι, component U P x a = component U P x b) : a = b := by
  apply (sectionsEquiv U P n).injective
  funext x
  simpa only [sectionsEquiv_apply] using h x

/-- Assemble the degree-zero cochain of any family of sections on the cover opens. -/
noncomputable def assembleVertices (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v'})
    (s : ∀ i, P.obj (op (U i))) : ((cechComplexFunctor U).obj P).X 0 :=
  (sectionsEquiv U P 0).symm (fun x => P.map (Pi.π (U ∘ x) 0).op (s (x 0)))

@[simp]
theorem vertex_assembleVertices (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v'})
    (s : ∀ i, P.obj (op (U i))) (i : ι) : vertex U P i (assembleVertices U P s) = s i := by
  unfold vertex singletonLift assembleVertices
  rw [ConcreteCategory.comp_apply, component_assemble, ← ConcreteCategory.comp_apply,
    ← P.map_comp, ← op_comp, Pi.lift_π]
  simp

/-- Component formula for an actual cochain, with the signs of the Mathlib horizontal differential. -/
theorem horizontal_apply (P : Cᵒᵖ ⥤ AddCommGrpCat.{max w v'}) {n : ℕ}
    (z : ((cechComplexFunctor U).obj P).X n) (x : Fin (n + 2) → ι) :
    (component U P x) (((cechComplexFunctor U).obj P).d n (n + 1) z) =
      ∑ j : Fin (n + 2), (-1 : ℤ) ^ (j : ℕ) •
        P.map (faceRestriction U x j).op (component U P (x ∘ j.succAbove) z) := by
  let ev : (((cechComplexFunctor U).obj P).X n ⟶ P.obj (op (intersection U x))) →+
      P.obj (op (intersection U x)) :=
    { toFun := fun f => f z
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have h := congrArg ev (component_d U P x)
  rw [map_sum] at h
  simpa only [map_zsmul] using h

/-- The intersection lies in each of its cover opens. -/
theorem intersection_le {L : Type u} [CompleteLattice L]
    (V : ι → L) {n : ℕ} (x : Fin (n + 1) → ι) (a : Fin (n + 1)) :
    intersection V x ≤ V (x a) :=
  leOfHom (Pi.π (V ∘ x) a)

/-- In a lattice of opens, Mathlib's categorical intersection is the actual infimum. -/
theorem intersection_eq_iInf {L : Type u} [CompleteLattice L]
    (V : ι → L) {n : ℕ} (x : Fin (n + 1) → ι) :
    intersection V x = ⨅ a, V (x a) := by
  apply le_antisymm
  · exact le_iInf (fun a => leOfHom (Pi.π (V ∘ x) a))
  · exact leOfHom (Pi.lift (f := V ∘ x) (fun a => homOfLE (iInf_le (V ∘ x) a)))

/-- All the simplex section rings for an affine cover of a scheme with affine
diagonal are affine, in every Čech degree. -/
theorem isAffineOpen_intersection {T : AlgebraicGeometry.Scheme.{u}}
    [AlgebraicGeometry.IsAffineHom (pullback.diagonal (terminal.from T))]
    (V : ι → T.Opens) (hV : ∀ i, AlgebraicGeometry.IsAffineOpen (V i))
    {n : ℕ} (x : Fin (n + 1) → ι) :
    AlgebraicGeometry.IsAffineOpen (intersection V x) := by
  rw [intersection_eq_iInf]
  exact AlgebraicGeometry.IsAffineOpen.iInf (fun a => hV (x a))

end CycleQ2.Cech

#print axioms CycleQ2.Cech.horizontal_apply

#print axioms CycleQ2.Cech.isAffineOpen_intersection
