import Proposal.GeometricLiteralOrbitBoundary
import Proposal.GeometricLiteralOrbitChernPullback
import Proposal.GeometricLiteralCotangentConnecting

/-!
# Connecting classes of the translated Cartier curves

The cotangent lift of the original Cartier cocycle pulls back along the
automorphism of the deformation. Iterating it gives representatives on the
actual inverse-image covers for both nontrivial translates.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralOrbitChernConnecting

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
  CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne
  CycleQ2FiniteCechConnecting CycleQ2LiteralNativeChernCocycle
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralNativeCupSectionValues CycleQ2LiteralNativeCupDerivedClass
  CycleQ2LiteralCotangentShortExact CycleQ2LiteralCotangentConnecting
  CycleQ2LiteralOrbitAction CycleQ2LiteralOrbitBoundary CycleQ2LiteralOrbitChern
  CycleQ2LiteralOrbitChernPullback
open CycleQ2FiniteCechOrbitPullback (push pullOne pullTwo pullOne_mapOne pull_boundary
  pullTwo_closed pullTwo_normalized)
open CycleQ2CechTwoToDerived (app)

variable {ι : Type}

private abbrev S := cotangentAdditiveComplex

local instance additiveHasExt : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0}
    (CycleQ2LiteralProjectiveCotangent.ClosedSurface : TopCat)) := HasExt.standard _

local instance schemeSheavesHasExt (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

section Transport

open CycleQ2GeometricDifferentialSheaf

variable (f : Surface ⟶ Surface)
  (hc : ∀ (U : Surface.Opens) (v : ℂ),
    f.app U (coefficientOn Surface.sheaf globalCoefficient U v) =
      coefficientOn Surface.sheaf globalCoefficient (f ⁻¹ᵁ U) v)
  (N : S.X₁ ⟶ push f.base S.X₁) (M : S.X₂ ⟶ push f.base S.X₂)
  (sq₁ : S.f ≫ M = N ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f.base).map S.f)
  (sq₂ : S.g ≫ differentialAddMap f hc = M ≫ (TopCat.Sheaf.pushforward AddCommGrpCat f.base).map S.g)

private def HasLift {U : ι → Surface.Opens} (d : One differentialAddSheaf U)
    (c : Two coefficientSheaf U) : Prop :=
  ∃ b : One S.X₂ U, mapOne U S.g b = d ∧ ∀ i j k W hi hj hk,
    boundaryValue S.X₂ U b i j k W hi hj hk = app S.f W (faceValue coefficientSheaf U c i j k W hi hj hk)

include sq₁ sq₂ in
private theorem pull_lift {U : ι → Surface.Opens} {d : One differentialAddSheaf U}
    {c : Two coefficientSheaf U} (h : HasLift d c) :
    HasLift (pullOne f.base (differentialAddMap f hc) U d)
      (pullTwo f.base N U c) := by
  obtain ⟨b, rfl, hb⟩ := h
  refine ⟨pullOne f.base M U b, ?_, ?_⟩
  · exact (pullOne_mapOne f.base U S.g S.g M
      (differentialAddMap f hc) sq₂ b).symm
  · exact pull_boundary (S := S) (T := S) f.base U
      N M sq₁ b c hb

/-- The normal two-cocycle for the first translated curve. -/
def translatedNativeCup : Two coefficientSheaf (translatedCover f) :=
  pullTwo f.base N cover nativeCupCocycle

/-- The normal two-cocycle for the second translated curve. -/
def twiceTranslatedNativeCup : Two coefficientSheaf (translatedCover (f ≫ f)) :=
  pullTwo f.base N (translatedCover f) (translatedNativeCup f N)

include sq₁ sq₂ in
private theorem firstLift :
    HasLift (translatedOne f (translatedCover f) id (fun _ => le_rfl)) (translatedNativeCup f N) := by
  have h := pull_lift f hc N M sq₁ sq₂ (U := cover) (d := chernOne) (c := nativeCupCocycle) exists_chernOne_nativeLift
  have he : pullOne f.base (differentialAddMap f hc) cover chernOne =
      translatedOne f (translatedCover f) id (fun _ => le_rfl) :=
    pullOne_chern f hc
  rw [he] at h
  exact h

include sq₁ sq₂ in
private theorem secondLift :
    HasLift (translatedOne (f ≫ f) (translatedCover (f ≫ f)) id (fun _ => le_rfl)) (twiceTranslatedNativeCup f N) := by
  have h := pull_lift f hc N M sq₁ sq₂ (firstLift f hc N M sq₁ sq₂)
  have he : pullOne f.base (differentialAddMap f hc) (translatedCover f)
      (translatedOne f (translatedCover f) id (fun _ => le_rfl)) =
      translatedOne (f ≫ f) (translatedCover (f ≫ f)) id (fun _ => le_rfl) :=
    pullOne_translated f hc f
  rw [he] at h
  exact h

private theorem connecting_of_lift (c : Two coefficientSheaf (translatedCover f))
    (hn : NormalizedTwo coefficientSheaf (translatedCover f) c)
    (hc : IsTwoCocycle coefficientSheaf (translatedCover f) c)
    (h : HasLift (translatedOne f (translatedCover f) id (fun _ => le_rfl)) c) :
    (translatedClass f).comp cotangentAdditiveShortExact.extClass rfl =
      cechTwoClass (translatedCover f) (translatedCover_top f) c hn hc := by
  obtain ⟨b, he, hb⟩ := h
  have hconn := cechOneClass_connecting (translatedCover f) cotangentAdditiveShortExact
    (translatedCover_top f) b c hn hc hb
  unfold translatedClass
  have hsymm := he.symm
  convert hconn using 1
  congr 2

/-- The derived class of the first translated normal two-cocycle. -/
def translatedCupClass : coefficientSheaf.H' 2 ⊤ :=
  cechTwoClass (translatedCover f) (translatedCover_top f)
    (translatedNativeCup f N)
    (pullTwo_normalized f.base N cover _ nativeCupCocycle_normalized)
    (pullTwo_closed f.base N cover _ nativeCupCocycle_closed)

/-- The derived class of the second translated normal two-cocycle. -/
def twiceTranslatedCupClass : coefficientSheaf.H' 2 ⊤ :=
  cechTwoClass (translatedCover (f ≫ f)) (translatedCover_top (f ≫ f))
    (twiceTranslatedNativeCup f N)
    (pullTwo_normalized f.base N (translatedCover f) _
      (pullTwo_normalized f.base N cover _ nativeCupCocycle_normalized))
    (pullTwo_closed f.base N (translatedCover f) _
      (pullTwo_closed f.base N cover _ nativeCupCocycle_closed))

include sq₁ sq₂ in
private theorem generic_translatedClass_connecting :
    (translatedClass f).comp cotangentAdditiveShortExact.extClass rfl = translatedCupClass f N :=
  connecting_of_lift _ _ _ _ (firstLift f hc N M sq₁ sq₂)

include sq₁ sq₂ in
private theorem generic_twiceTranslatedClass_connecting :
    (translatedClass (f ≫ f)).comp cotangentAdditiveShortExact.extClass rfl =
      twiceTranslatedCupClass f N :=
  connecting_of_lift _ _ _ _ (secondLift f hc N M sq₁ sq₂)

end Transport

variable (z : ℂ) (hz : z ^ 3 = 1)

private abbrev g := (closedProjectiveAction z hz).hom

theorem translatedClass_connecting_native :
    (translatedClass (g z hz)).comp cotangentAdditiveShortExact.extClass rfl =
      translatedCupClass (g z hz) (additiveNormal z hz) :=
  generic_translatedClass_connecting (g z hz) (surfaceCoefficient z hz)
    (additiveNormal z hz) (additiveMiddle z hz) (additive_inclusion_comm z hz) (additive_reduction_comm z hz)

theorem twiceTranslatedClass_connecting_native :
    (translatedClass (g z hz ≫ g z hz)).comp cotangentAdditiveShortExact.extClass rfl =
      twiceTranslatedCupClass (g z hz) (additiveNormal z hz) :=
  generic_twiceTranslatedClass_connecting (g z hz) (surfaceCoefficient z hz)
    (additiveNormal z hz) (additiveMiddle z hz) (additive_inclusion_comm z hz) (additive_reduction_comm z hz)

private theorem connecting_sum {C : Type*} [Category* C] [Abelian C] [HasExt.{1} C]
    {X Y Z : C} (t : Ext Y Z 1) (u a b c : Ext X Y 1)
    (x y w : Ext X Z 2) (hu : u = a + b + c)
    (ha : a.comp t rfl = x) (hb : b.comp t rfl = y) (hc : c.comp t rfl = w) :
    u.comp t rfl = x + y + w := by
  subst u x y w
  rw [Ext.add_comp, Ext.add_comp]

/-- The connecting class of the product of all three systems of transition
units is represented by the original cup and its two actual normal pullbacks. -/
theorem orbitDerivedClass_connecting_native :
    (orbitDerivedClass z hz).comp cotangentAdditiveShortExact.extClass rfl =
      nativeCupDerivedClass + translatedCupClass (g z hz) (additiveNormal z hz) +
        twiceTranslatedCupClass (g z hz) (additiveNormal z hz) :=
  connecting_sum cotangentAdditiveShortExact.extClass (orbitDerivedClass z hz) CycleQ2LiteralSheafOneClasses.chernDerivedClass
    (translatedClass (g z hz)) (translatedClass (g z hz ≫ g z hz)) nativeCupDerivedClass
    (translatedCupClass (g z hz) (additiveNormal z hz))
    (twiceTranslatedCupClass (g z hz) (additiveNormal z hz))
    (orbitDerivedClass_eq_sum z hz) chernDerivedClass_connecting_native
    (translatedClass_connecting_native z hz) (twiceTranslatedClass_connecting_native z hz)

end CycleQ2LiteralOrbitChernConnecting

end

#print axioms CycleQ2LiteralOrbitChernConnecting.translatedClass_connecting_native
#print axioms CycleQ2LiteralOrbitChernConnecting.twiceTranslatedClass_connecting_native
#print axioms CycleQ2LiteralOrbitChernConnecting.orbitDerivedClass_connecting_native
