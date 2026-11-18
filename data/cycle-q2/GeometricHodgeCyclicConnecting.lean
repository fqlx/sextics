import Proposal.GeometricHodgeCompactOneCocycles
import Proposal.GeometricLiteralAbelJacobiQPullbackDerived

/-! # Pullback of the connecting class of an actual section

For an automorphism of a compact space, inverse-image pullback on derived
degree one agrees with the canonical direct-image comparison for an
equivalence. Applying this to a morphism of short exact sequences identifies
the transformed boundary with the boundary of the transformed section.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCyclicConnecting
open CategoryTheory CategoryTheory.Abelian TopologicalSpace
  CycleQ2AutomorphismGlobalSections CycleQ2InjectiveCech CycleQ2CechTwoToDerived
  CycleQ2FiniteCechOrbitPullback CycleQ2GeometricSheafLocalIso
  CycleQ2GeometricConeCech.HZero CycleQ2FiniteCechHOne

variable {X : TopCat.{0}}
local instance (T : TopCat.{0}) : HasExt.{1} (AbSheaf T) := HasExt.standard _

theorem section_zero {F : AbSheaf X} (U : Opens X) (s : Sections F U) :
    sectionExtZero U s = (sectionsEquiv F U).symm s := by
  apply (sectionsEquiv F U).injective
  rw [AddEquiv.apply_symm_apply, sectionExtZero, sectionsEquiv_mk₀]
  exact (freeOpenSections F U).apply_symm_apply s

theorem compare [CompactSpace X] (h : X ≅ X) {B D : AbSheaf X}
    (f : B ⟶ (pushFunctor h).obj D) (x : B.H' 1 ⊤) :
    CycleQ2LiteralAbelJacobiQPullbackDerived.pullH h.hom f 1 x =
      CycleQ2AutomorphismCohomology.pullH h f 1 x := by
  obtain ⟨t,U,hU,c,hc,rfl⟩ := CycleQ2HodgeCompactOneCocycles.representative B x
  rw [CycleQ2LiteralAbelJacobiQPullbackDerived.pullH_cech,
    CycleQ2AutomorphismCohomology.pullH_cechOneClass h U hU
      (cover_top h.hom U hU)]

theorem naturality [CompactSpace X] {Y : TopCat.{0}} (g : Y ⟶ X)
    {A B : AbSheaf X} {C D : AbSheaf Y} (f : A ⟶ B) (k : C ⟶ D)
    (α : A ⟶ push g C) (β : B ⟶ push g D)
    (h : f ≫ β = α ≫ (TopCat.Sheaf.pushforward AddCommGrpCat g).map k) (x : A.H' 1 ⊤) :
    CycleQ2LiteralAbelJacobiQPullbackDerived.pullH g β 1 (x.comp (Ext.mk₀ f) (add_zero 1)) =
      (CycleQ2LiteralAbelJacobiQPullbackDerived.pullH g α 1 x).comp (Ext.mk₀ k) (add_zero 1) := by
  obtain ⟨t,U,hU,b,hb,rfl⟩ := CycleQ2HodgeCompactOneCocycles.representative A x
  rw [cechOneClass_naturality, CycleQ2LiteralAbelJacobiQPullbackDerived.pullH_cech,
    CycleQ2LiteralAbelJacobiQPullbackDerived.pullH_cech, cechOneClass_naturality]
  congr 1
  exact pullOne_mapOne g U f k α β h b

theorem pull_section (h : X ≅ X) {B D : AbSheaf X} (f : B ⟶ (pushFunctor h).obj D)
    (s : Sections B ⊤) : CycleQ2AutomorphismCohomology.pullH h f 0 (sectionExtZero ⊤ s) =
      sectionExtZero (F := D) ⊤ (app f ⊤ s) := by
  apply (CycleQ2AutomorphismCohomology.pushH h D 0).injective
  change (CycleQ2AutomorphismCohomology.pushH h D 0)
    ((CycleQ2AutomorphismCohomology.pushH h D 0).symm _) = _
  rw [AddEquiv.apply_symm_apply]
  exact (CycleQ2CechTwoComparison.sectionExtZero_app f ⊤ s).symm.trans
    (sourceIso_sectionExtZero h D (app f ⊤ s)).symm

theorem connecting [CompactSpace X] (h : X ≅ X) {S T : ShortComplex (AbSheaf X)}
    (hS : S.ShortExact) (hT : T.ShortExact) (f : S ⟶ T.map (pushFunctor h)) (s : Sections S.X₃ ⊤) :
    CycleQ2LiteralAbelJacobiQPullbackDerived.pullH h.hom f.τ₁ 1
      (((sectionsEquiv S.X₃ ⊤).symm s).comp hS.extClass rfl) =
    ((sectionsEquiv T.X₃ ⊤).symm (app f.τ₃ ⊤ s)).comp hT.extClass rfl := by
  rw [compare h, ← section_zero, ← section_zero,
    ← CycleQ2AutomorphismCohomology.pullH_connecting h hS hT f 0 (sectionExtZero ⊤ s),
    pull_section] <;> rfl

end CycleQ2HodgeCyclicConnecting
end

#print axioms CycleQ2HodgeCyclicConnecting.connecting
