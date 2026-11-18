import Proposal.ScratchCechDeRhamTotalThree
import Proposal.ScratchCechComplexEval
import Mathlib.Algebra.Category.Grp.Limits
import Mathlib.Algebra.Category.Grp.Preadditive

/-!
# Čech total de Rham cohomology and restriction

The horizontal complexes are Mathlib's Čech complexes of the presheaves of
forms. The successive natural transformations are the differentials of the
presheaf complex. Restriction to one cover member sends every total boundary
to the derivative of its vertex two-form.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CycleQ2CechDeRhamTotalThree

namespace CycleQ2.Cech

universe u v w
variable {C : Type u} [Category.{v} C] [HasFiniteProducts C]
    {ι : Type w} (U : ι → C)
    (D : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{w}) ℕ)

abbrev row (q : ℕ) := (cechComplexFunctor U).obj (D.X q)

lemma cochainMap_zero {P Q : Cᵒᵖ ⥤ AddCommGrpCat.{w}} (p : ℕ) :
    ((cechComplexFunctor U).map (0 : P ⟶ Q)).f p = 0 := by
  apply component_ext U Q
  intro x
  rw [component_naturality]
  simp

/-- The Čech rows of the given presheaf complex, with their induced vertical
maps. Evaluating the composition of vertical maps uses the product projections
on the intersections of the cover. -/
def presheafDouble : Double.{w} where
  X p q := (row U D q).X p
  h p q := ((row U D q).d p (p+1)).hom
  v p q := (((cechComplexFunctor U).map (D.d q (q+1))).f p).hom
  hh p q x := by
    exact ConcreteCategory.congr_hom ((row U D q).d_comp_d p (p+1) (p+2)) x
  vv p q x := by
    have h := congrArg (fun f => (f : (row U D q) ⟶ (row U D (q+2))).f p)
      ((cechComplexFunctor U).map_comp (D.d q (q+1)) (D.d (q+1) (q+2)))
    rw [D.d_comp_d, cochainMap_zero] at h
    exact ConcreteCategory.congr_hom h.symm x
  hv p q x := by
    exact ConcreteCategory.congr_hom (((cechComplexFunctor U).map (D.d q (q+1))).comm p (p+1)) x

/-- An actual vertex primitive, evaluated in the presheaf of two-forms on the
specified member of the cover. -/
theorem vertexExact (i : ι) (z : Cycles (presheafDouble U D))
    (hz : classOf _ z = 0) :
    ∃ a : (D.X 2).obj (op (U i)),
      (D.d 2 3).app (op (U i)) a = vertex U (D.X 3) i z.1.1 := by
  obtain ⟨x,hx⟩ := vertex_exact _ z hz
  refine ⟨vertex U (D.X 2) i x, ?_⟩
  rw [← hx]
  exact (ConcreteCategory.congr_hom (vertex_naturality U (D.d 2 3) i) x).symm

/-- The group of three-forms on the cover member modulo exact three-forms.
The image of a total cocycle is closed by `d3` and naturality. -/
abbrev VertexQuotient (i : ι) :=
  (D.X 3).obj (op (U i)) ⧸ ((D.d 2 3).app (op (U i))).hom.range

/-- Projection of total de Rham cohomology to vertex three-forms modulo exact
ones. This uses the full degree-two group of boundaries on the cover. -/
def vertexClassMap (i : ι) :
    HThree (presheafDouble U D) →+ VertexQuotient U D i :=
  let q := QuotientAddGroup.mk' ((D.d 2 3).app (op (U i))).hom.range
  vertexMap _ (q.comp (vertex U (D.X 3) i).hom) (by
    intro a
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact ⟨vertex U (D.X 2) i a,
      (ConcreteCategory.congr_hom (vertex_naturality U (D.d 2 3) i) a).symm⟩)

@[simp] theorem vertexClassMap_classOf (i : ι) (z : Cycles (presheafDouble U D)) :
    vertexClassMap U D i (classOf _ z) = QuotientAddGroup.mk (vertex U (D.X 3) i z.1.1) := rfl

end CycleQ2.Cech
end

#print axioms CycleQ2.Cech.presheafDouble
#print axioms CycleQ2.Cech.vertexExact
#print axioms CycleQ2.Cech.vertexClassMap_classOf
