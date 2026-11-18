import Proposal.GeometricCartierDerivedClass
import Proposal.GeometricAffineCohomology
import Proposal.GeometricDifferentialSheaf
import Proposal.GeometricModuleLocalIso
import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# Global one-forms in the two-term de Rham complex

The mapping cone of the genuine Kähler derivative, with functions and
one-forms originally in degree zero, places them in degrees minus one
and zero. A section of the one-form sheaf gives a map into that cone in
the derived category. It vanishes exactly when a global regular
function on the same scheme has that differential. For a smooth curve
this is the degree-one class of the de Rham complex.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2CurveDeRhamOne

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricDifferentialSheaf
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2CechTwoToDerived (app freeOpenSections_postcomp)
attribute [local instance] HasDerivedCategory.standard

variable (X : Scheme.{0}) (c : ℂ →+* Γ(X, ⊤))

abbrev OneForms := addSheaf (differentialSheaf X.sheaf c)

/-- The actual Kähler differential as an additive morphism of sheaves. -/
def derivative : structureAdditiveSheaf X ⟶ OneForms X c where
  hom := {
    app U := AddCommGrpCat.ofHom ((universalDifferential X.sheaf c).d (X := U))
    naturality {U V} h := by
      ext x
      exact (universalDifferential X.sheaf c).d_map h x }

private abbrev Single := CochainComplex.singleFunctor (AbSheaf (show TopCat from X)) 0
private abbrev triangle :=
  DerivedCategory.Q.mapTriangle.obj (CochainComplex.mappingCone.triangle
    ((Single X).map (derivative X c)))

/-- The cone is placed so its morphisms from sections compute degree one. -/
def formClass (ω : Sections (OneForms X c) ⊤) :
    (DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0).obj (freeOpen ⊤) ⟶
      (triangle X c).obj₃ :=
  (DerivedCategory.singleFunctor _ 0).map ((freeOpenSections _ ⊤).symm ω) ≫ (triangle X c).mor₂

theorem formClass_eq_zero_iff (ω : Sections (OneForms X c) ⊤) :
    formClass X c ω = 0 ↔ ∃ f : Γ(X, ⊤), (universalDifferential X.sheaf c).d f = ω := by
  let T := triangle X c
  let E := DerivedCategory.singleFunctor (AbSheaf (show TopCat from X)) 0
  let a := (freeOpenSections (OneForms X c) ⊤).symm ω
  have hT := DerivedCategory.mappingCone_triangle_distinguished ((Single X).map (derivative X c))
  constructor
  · intro h
    obtain ⟨b,hb⟩ := Pretriangulated.Triangle.coyoneda_exact₂ T hT (E.map a) h
    obtain ⟨v,hv⟩ := E.map_surjective b
    have he : a = v ≫ derivative X c := E.map_injective (by
      rw [Functor.map_comp, hv]
      exact hb)
    refine ⟨freeOpenSections (structureAdditiveSheaf X) ⊤ v, ?_⟩
    exact (freeOpenSections_postcomp ⊤ v (derivative X c)).trans
      ((congrArg (freeOpenSections _ ⊤) he).symm.trans (AddEquiv.apply_symm_apply _ _))
  · rintro ⟨f,hf⟩
    let v := (freeOpenSections (structureAdditiveSheaf X) ⊤).symm f
    have ha : a = v ≫ derivative X c := by
      apply (freeOpenSections _ ⊤).injective
      rw [← freeOpenSections_postcomp ⊤ v (derivative X c)]
      exact (AddEquiv.apply_symm_apply _ _).trans (hf.symm.trans
        (congrArg (app (derivative X c) ⊤) (AddEquiv.apply_symm_apply _ f)).symm)
    change E.map a ≫ T.mor₂ = 0
    rw [ha, Functor.map_comp, Category.assoc]
    change E.map v ≫ T.mor₁ ≫ T.mor₂ = 0
    rw [Pretriangulated.comp_distTriang_mor_zero₁₂ _ hT, comp_zero]

theorem formClass_ne_zero_of_constants (hc : Function.Surjective c)
    (ω : Sections (OneForms X c) ⊤) (hω : ω ≠ 0) : formClass X c ω ≠ 0 := by
  intro h
  obtain ⟨f,hf⟩ := (formClass_eq_zero_iff X c ω).mp h
  obtain ⟨z,rfl⟩ := hc f
  have hz : coefficientOn X.sheaf c ⊤ z = c z :=
    ConcreteCategory.congr_hom (X.presheaf.map_id (op ⊤)) _
  exact hω (hf.symm.trans ((congrArg (universalDifferential X.sheaf c).d hz.symm).trans
    ((universalDifferential X.sheaf c).d_app (X := op ⊤) z)))

end CycleQ2CurveDeRhamOne
end

#print axioms CycleQ2CurveDeRhamOne.formClass_eq_zero_iff
#print axioms CycleQ2CurveDeRhamOne.formClass_ne_zero_of_constants
