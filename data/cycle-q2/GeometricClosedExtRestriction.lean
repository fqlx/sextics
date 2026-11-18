import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map
import Mathlib.AlgebraicGeometry.Modules.Sheaf
import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
import Mathlib.Topology.Sheaves.SheafCondition.Sites

/-!
# Module extensions supported on a closed subscheme

For a closed immersion the direct image of any module restricts to zero
on its open complement. Precomposing a module extension with a morphism
to that direct image therefore gives a class supported on the same closed
subscheme, over an arbitrary coefficient field or base.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2ClosedExtRestriction

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace
variable {Z X : Scheme.{0}}

instance (priority := low) restrictFiniteLimits (u : Z ⟶ X) [IsOpenImmersion u] :
    PreservesFiniteLimits (Scheme.Modules.restrictFunctor u) := by
  let F := Scheme.Modules.toPresheaf Z
  have : ReflectsLimits F := reflectsLimits_of_reflectsIsomorphisms
  let W := (Functor.whiskeringLeft Z.Opensᵒᵖ X.Opensᵒᵖ AddCommGrpCat.{0}).obj u.opensFunctor.op
  have : PreservesFiniteLimits W :=
    ⟨fun _ => inferInstanceAs (PreservesLimitsOfShape _ ((Functor.whiskeringLeft _ _ _).obj u.opensFunctor.op))⟩
  have : PreservesFiniteLimits (Scheme.Modules.toPresheaf X ⋙ W) := comp_preservesFiniteLimits _ _
  have e : Scheme.Modules.restrictFunctor u ⋙ F ≅ Scheme.Modules.toPresheaf X ⋙ W := Iso.refl _
  have : PreservesFiniteLimits (Scheme.Modules.restrictFunctor u ⋙ F) :=
    preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ F

instance (priority := low) restrictAdditive (u : Z ⟶ X) [IsOpenImmersion u] :
    (Scheme.Modules.restrictFunctor u).Additive where

variable (i : Z ⟶ X) [IsClosedImmersion i]

def off : X.Opens :=
  ⟨(Set.range i)ᶜ,i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

theorem pushforward_off_closed (F : Z.Modules) :
    IsZero ((Scheme.Modules.restrictFunctor (off i).ι).obj ((Scheme.Modules.pushforward i).obj F)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro W
  apply ConcreteCategory.hom_ext
  intro s
  let A : (show TopCat from Z).Sheaf AddCommGrpCat.{0} := (SheafOfModules.toSheaf Z.ringCatSheaf).obj F
  have hW : i ⁻¹ᵁ ((off i).ι ''ᵁ W.unop) = ⊥ := by
    apply bot_unique
    rintro z ⟨y,-,hy⟩
    exact y.property ⟨z,hy.symm⟩
  exact (AddCommGrpCat.isZero_iff_subsingleton.mp
    (TopCat.Sheaf.isTerminalOfEqEmpty A hW).isZero).elim _ _

attribute [local instance] HasExt.standard

theorem supportedPrecomp_restrict {E W : X.Modules} {F : Z.Modules}
    (φ : E ⟶ (Scheme.Modules.pushforward i).obj F) {n : ℕ}
    (e : Ext.{1} ((Scheme.Modules.pushforward i).obj F) W n) :
    ((Ext.mk₀ φ).comp e (zero_add n)).mapExactFunctor (Scheme.Modules.restrictFunctor (off i).ι) = 0 := by
  let R := Scheme.Modules.restrictFunctor (off i).ι
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    (pushforward_off_closed i F).eq_of_tgt (R.map φ) 0, Ext.mk₀_zero, Ext.zero_comp]

end CycleQ2ClosedExtRestriction
end

#print axioms CycleQ2ClosedExtRestriction.pushforward_off_closed
#print axioms CycleQ2ClosedExtRestriction.supportedPrecomp_restrict
