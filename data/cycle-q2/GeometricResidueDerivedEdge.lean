import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful

/-!
# From a vanishing derived class to its cokernel section

Projecting a cochain complex to the cokernel of its incoming differential
in degree `n` detects a necessary condition for a degree-`n` class to
vanish in the derived category. The projection is a chain map, so this
implication also applies to complexes with nonzero higher terms.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
universe w v u
namespace CycleQ2GeometricResidueDerivedEdge

open CategoryTheory CategoryTheory.Limits HomologicalComplex

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- The chain map to the incoming cokernel concentrated in degree `n`. -/
def cokernelProjection (K : CochainComplex C ℤ) (n : ℤ) :
    K ⟶ (single C (ComplexShape.up ℤ) n).obj (cokernel (K.d (n - 1) n)) :=
  mkHomToSingle (cokernel.π (K.d (n - 1) n)) (fun i hi => by
    change i + 1 = n at hi
    have h : i = n - 1 := by omega
    subst i
    exact cokernel.condition _)

/-- A cocycle which gives the zero morphism in the derived category also gives
zero after the canonical map to the incoming cokernel. -/
theorem comp_cokernel_eq_zero_of_derived_zero
    (K : CochainComplex C ℤ) (n : ℤ) {A : C} (α : A ⟶ K.X n)
    (hα : ∀ j : ℤ, (ComplexShape.up ℤ).Rel n j → α ≫ K.d n j = 0)
    (hzero : DerivedCategory.Q.map (mkHomFromSingle α hα) = 0) :
    α ≫ cokernel.π (K.d (n - 1) n) = 0 := by
  have hcomp : mkHomFromSingle α hα ≫ cokernelProjection K n =
      (single C (ComplexShape.up ℤ) n).map (α ≫ cokernel.π (K.d (n - 1) n)) := by
    apply from_single_hom_ext
    simp [cokernelProjection, single_map_f_self]
  apply (DerivedCategory.singleFunctor C n).map_injective
  rw [Functor.map_zero]
  change DerivedCategory.Q.map
    ((single C (ComplexShape.up ℤ) n).map (α ≫ cokernel.π (K.d (n - 1) n))) = 0
  rw [← hcomp, Functor.map_comp, hzero, zero_comp]

end CycleQ2GeometricResidueDerivedEdge
end

#print axioms CycleQ2GeometricResidueDerivedEdge.comp_cokernel_eq_zero_of_derived_zero
