import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-! Projections from the Mathlib Čech complex to the sections on an intersection.
In degree zero, the singleton intersection is canonically the chosen cover open. -/

set_option backward.isDefEq.respectTransparency false

open CategoryTheory CategoryTheory.Limits Opposite

namespace CycleQ2.Cech

universe w v v' u u'

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    {A : Type u'} [Category.{v'} A] [HasProducts.{w} A] [Preadditive A]
    {ι : Type w} (U : ι → C)

/-- The intersection object corresponding to the ordered tuple of cover indices. -/
noncomputable abbrev intersection {n : ℕ} (x : Fin (n + 1) → ι) : C :=
  ∏ᶜ (U ∘ x)

/-- Projection of a Mathlib Čech cochain to the sections on one intersection. -/
noncomputable def component (P : Cᵒᵖ ⥤ A) {n : ℕ} (x : Fin (n + 1) → ι) :
    ((cechComplexFunctor U).obj P).X n ⟶ P.obj (op (intersection U x)) :=
  Pi.π (fun y : Fin (n + 1) → ι => P.obj (op (intersection U y))) x

@[reassoc]
theorem component_naturality {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q)
    {n : ℕ} (x : Fin (n + 1) → ι) :
    ((cechComplexFunctor U).map f).f n ≫ component U Q x =
      component U P x ≫ f.app (op (intersection U x)) := by
  exact Pi.map_π (fun y : Fin (n + 1) → ι => f.app (op (intersection U y))) x

theorem component_ext (P : Cᵒᵖ ⥤ A) {n : ℕ} {V : A}
    {a b : V ⟶ ((cechComplexFunctor U).obj P).X n}
    (h : ∀ x : Fin (n + 1) → ι, a ≫ component U P x = b ≫ component U P x) :
    a = b :=
  Pi.hom_ext (f := fun x : Fin (n + 1) → ι => P.obj (op (intersection U x))) a b h

/-- The canonical arrow from one cover object to its singleton intersection. -/
noncomputable def singletonLift (i : ι) : U i ⟶ intersection U (fun _ : Fin 1 => i) :=
  Pi.lift (f := fun _ : Fin 1 => U i) (fun _ => 𝟙 (U i))

/-- Restriction to the chosen open, including the canonical map to its singleton intersection. -/
noncomputable def vertex (P : Cᵒᵖ ⥤ A) (i : ι) :
    ((cechComplexFunctor U).obj P).X 0 ⟶ P.obj (op (U i)) :=
  component U P (fun _ : Fin 1 => i) ≫
    P.map (singletonLift U i).op

@[reassoc]
theorem vertex_naturality {P Q : Cᵒᵖ ⥤ A} (f : P ⟶ Q) (i : ι) :
    ((cechComplexFunctor U).map f).f 0 ≫ vertex U Q i =
      vertex U P i ≫ f.app (op (U i)) := by
  simp only [vertex, Category.assoc, component_naturality_assoc, f.naturality]

/-- Evaluation at the selected vertex as a natural transformation on all presheaves. -/
noncomputable def vertexNat (i : ι) :
    cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) 0 ⟶
      (evaluation Cᵒᵖ A).obj (op (U i)) where
  app P := vertex U P i
  naturality f := vertex_naturality U f i

end CycleQ2.Cech

#print axioms CycleQ2.Cech.vertexNat
