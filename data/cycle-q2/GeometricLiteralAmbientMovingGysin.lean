import Proposal.GeometricLiteralThreefoldCanonicalFrame
import Proposal.GeometricLiteralAmbientCubicCanonical
import Proposal.GeometricLiteralMovingModuleResidue

/-!
# The successive module residue extension of the actual moving curve

The two Cartier inclusions Γ ⊂ D ⊂ T give a Yoneda two-extension on T.
Its right-hand coefficient is the direct image of actual Kähler one-forms
of Γ. Its left-hand coefficient is the structure sheaf of the fixed threefold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingModuleCartier

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
open CycleQ2SurfaceCoordinateFrames (Surface)
open CycleQ2LiteralMovingResidueExact
open CycleQ2SeedSectionAffineInjective (ChartRegular)
private abbrev underlyingSequence (t : Fin 3 → ℂ) :=
  @ShortComplex.map _ _ _ _ _ _
    (show ShortComplex (SheafOfModules.{0} Surface.ringCatSheaf) from sequence t)
    (SheafOfModules.toSheaf.{0} Surface.ringCatSheaf) (CycleQ2LiteralSweptExtSupport.forgetPreservesZero Surface)

def additiveSequenceIso (t : Fin 3 → ℂ) : underlyingSequence t ≅ residueComplex t :=
  ShortComplex.isoMk (Iso.refl _) (Iso.refl _) (quotientAddIso t) (by simp [sequence,residueComplex])
    (by simpa [sequence,residueComplex] using (projection_quotientAddIso t).symm)

local instance : HasExt.{1} (TopCat.Sheaf AddCommGrpCat.{0} (show TopCat from Surface)) :=
  HasExt.standard _
local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0}) :=
  HasExt.standard _

set_option maxHeartbeats 1200000 in
theorem extClass_comparison (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    (CycleQ2LiteralSweptExtSupport.additiveShortExact (shortExact t ht)).extClass =
      (Ext.mk₀ (quotientAddIso t).hom).comp (residueShortExact t ht).extClass (zero_add 1) := by
  let e := (additiveSequenceIso t).hom
  have e₁ : e.τ₁ = 𝟙 _ := rfl
  have e₃ : e.τ₃ = (quotientAddIso t).hom := rfl
  have h := ShortComplex.ShortExact.extClass_naturality
    (CycleQ2LiteralSweptExtSupport.additiveShortExact (shortExact t ht)) (residueShortExact t ht) e
  rw [e₁,e₃,Ext.comp_mk₀_id] at h
  exact h

end CycleQ2LiteralMovingModuleCartier

namespace CycleQ2LiteralAmbientMovingGysin

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian TopologicalSpace
open CycleQ2LiteralAmbientCubicSequence (T structureOn)
open CycleQ2LiteralAmbientCubicCanonical (canonicalSequence canonicalSequence_shortExact)
open CycleQ2LiteralMovingModuleCartier (ambientSurface onThreefold onThreefold_shortExact)
open CycleQ2LiteralMovingModuleResidue (curveModule moduleResidue moduleResidue_additive)
open CycleQ2SeedSectionAffineInjective (ChartRegular)

local instance : HasExt.{1} T.Modules := HasExt.standard _
abbrev directCurveForms (t : Fin 3 → ℂ) := (Scheme.Modules.pushforward ambientSurface).obj (curveModule t)

/-- The class in module Ext of the successive Cartier extensions. -/
def curveGysin (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    Ext.{1} (directCurveForms t) (structureOn T) 2 :=
  ((Ext.mk₀ ((Scheme.Modules.pushforward ambientSurface).map (moduleResidue t ht))).comp
    (onThreefold_shortExact t ht).extClass (zero_add 1)).comp canonicalSequence_shortExact.extClass rfl

/-- The same module two-extension with values in the actual top-form sheaf,
using the canonical volume on this incidence fiber. -/
def curveGysinVolume (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    Ext.{1} (directCurveForms t) CycleQ2LiteralSweptExtSupport.canonicalModule 2 :=
  (curveGysin t ht).comp (Ext.mk₀ CycleQ2LiteralThreefoldCanonicalFrame.volumeIso.hom) (add_zero 2)

open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2ClosedEmbeddingCohomology CycleQ2ClosedEmbeddingSheafExact
open CycleQ2LiteralMovingResidueCurve CycleQ2LiteralMovingResidueExact
open CycleQ2SeedSectionSheafCurveBinding (curveToSurface)
open CycleQ2SurfaceCoordinateFrames (Surface CanonicalForms)
open CycleQ2LiteralMovingModuleCartier (inclusion quotientAddIso)
local instance (Z : Scheme.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}) :=
  HasExt.standard _
local instance (Z : TopCat.{0}) : HasExt.{1} (Z.Sheaf AddCommGrpCat.{0}) := HasExt.standard _
local instance : IsClosedImmersion ambientSurface :=
  CycleQ2LiteralAmbientSurface.surfaceToFiber_isClosedImmersion
attribute [local instance] CycleQ2LiteralSweptExtSupport.forgetFiniteColimits

private abbrev F := SheafOfModules.toSheaf.{0} T.ringCatSheaf
private instance : F.Additive where

private theorem push_naturality {A B : TopCat.{0}} (f : A ⟶ B) (hf : Topology.IsClosedEmbedding f)
    {M N : A.Sheaf AddCommGrpCat.{0}} (u : M ⟶ N) (n : ℕ) (x : M.H' n ⊤) :
    pushHEquiv f hf N n (x.comp (Ext.mk₀ u) (add_zero n)) =
      (pushHEquiv f hf M n x).comp (Ext.mk₀ ((push f).map u)) (add_zero n) := by
  letI := push_preservesFiniteColimits f hf
  change (Ext.mk₀ _).comp ((x.comp (Ext.mk₀ u) (add_zero n)).mapExactFunctor (push f)) _ =
    ((Ext.mk₀ _).comp (x.mapExactFunctor (push f)) _).comp _ _
  rw [Ext.mapExactFunctor_comp,Ext.mapExactFunctor_mk₀,Ext.comp_assoc_of_third_deg_zero]

/-- The moving class in the module residue row gives its previously computed
additive boundary on D. -/
private theorem moving_boundary (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (b : (addSheaf (curveModule t)).H' 1 ⊤) :
    (b.comp (Ext.mk₀ (CycleQ2LiteralMovingModuleCartier.forgetModules.map (moduleResidue t ht)))
      (add_zero 1)).comp
        (CycleQ2LiteralSweptExtSupport.additiveShortExact (CycleQ2LiteralMovingModuleCartier.shortExact t ht)).extClass rfl =
      residueConnecting t ht ⊤ (b.comp (Ext.mk₀ (curveResidue t ht)) (add_zero 1)) := by
  rw [residueConnecting_apply,CycleQ2LiteralMovingModuleCartier.extClass_comparison]
  rw [← Ext.comp_assoc_of_second_deg_zero,Ext.comp_assoc_of_third_deg_zero,Ext.mk₀_comp_mk₀,
    moduleResidue_additive]

/-- The cohomological direct image of one-forms on Γ, along both closed
inclusions, expressed with its actual module coefficient on T. -/
def ambientClass (t : Fin 3 → ℂ) (x : (curveForms t).H' 1 ⊤) :
    (addSheaf (directCurveForms t)).H' 1 ⊤ :=
  pushHEquiv ambientSurface.base ambientSurface.isClosedEmbedding (addSheaf (curveModule t)) 1
    (pushHEquiv (curveToSurface t).base (curveToSurface t).isClosedEmbedding (curveForms t) 1 x)

/-- On every genuine curve class, forgetting the module two-extension and
taking its Yoneda product is the iterated additive residue. -/
theorem curveGysin_pairing (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (x : (curveForms t).H' 1 ⊤) :
    (ambientClass t x).comp ((curveGysin t ht).mapExactFunctor F) rfl =
      CycleQ2LiteralAmbientCubicCanonical.iteratedResidue t ht x := by
  let b := pushHEquiv (curveToSurface t).base (curveToSurface t).isClosedEmbedding (curveForms t) 1 x
  let u := CycleQ2LiteralMovingModuleCartier.forgetModules.map (moduleResidue t ht)
  let hS := CycleQ2LiteralSweptExtSupport.additiveShortExact (CycleQ2LiteralMovingModuleCartier.shortExact t ht)
  unfold curveGysin
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    Ext.mapExactFunctor_extClass, Ext.mapExactFunctor_extClass,
    ← Ext.comp_assoc _ _ _ rfl rfl rfl, ← Ext.comp_assoc_of_second_deg_zero]
  apply congrArg (fun a : (addSheaf ((Scheme.Modules.pushforward ambientSurface).obj CanonicalForms)).H' 2 ⊤ =>
    a.comp CycleQ2LiteralAmbientCubicCanonical.additiveSequence_shortExact.extClass rfl)
  change (((pushHEquiv ambientSurface.base ambientSurface.isClosedEmbedding _ 1 b).comp
    (Ext.mk₀ ((push ambientSurface.base).map u)) (add_zero 1)).comp
    (pushShortExact ambientSurface.base ambientSurface.isClosedEmbedding hS).extClass rfl) =
    pushHEquiv ambientSurface.base ambientSurface.isClosedEmbedding _ 2
      (residueConnecting t ht ⊤ (b.comp (Ext.mk₀ (curveResidue t ht)) (add_zero 1)))
  rw [← push_naturality, ← pushHEquiv_connecting]
  exact congrArg (pushHEquiv ambientSurface.base ambientSurface.isClosedEmbedding _ 2) (moving_boundary t ht b)

theorem curveGysin_ne_zero (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (hv : Subsingleton ((addSheaf CycleQ2LiteralAmbientCubicSequence.O3).H' 2 ⊤)) :
    curveGysin t ht ≠ 0 := by
  intro hz
  apply CycleQ2LiteralAmbientCubicCanonical.movingSurfaceConnecting_ne_zero t ht hv
  rw [← CycleQ2LiteralAmbientCubicCanonical.iteratedResidue_curveClass,
    ← curveGysin_pairing, hz,Ext.mapExactFunctor_zero,Ext.comp_zero]

/-- After using the literal volume form, pairing with the two-extension
still gives the same iterated boundary, now as a top-form class. -/
theorem curveGysinVolume_pairing (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (x : (curveForms t).H' 1 ⊤) :
    (ambientClass t x).comp ((curveGysinVolume t ht).mapExactFunctor F) rfl =
      (CycleQ2LiteralAmbientCubicCanonical.iteratedResidue t ht x).comp
        (Ext.mk₀ (F.map CycleQ2LiteralThreefoldCanonicalFrame.volumeIso.hom)) (add_zero 3) := by
  rw [curveGysinVolume, Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀,
    ← Ext.comp_assoc_of_third_deg_zero, curveGysin_pairing]

end CycleQ2LiteralAmbientMovingGysin
end

#print axioms CycleQ2LiteralAmbientMovingGysin.curveGysin
#print axioms CycleQ2LiteralAmbientMovingGysin.curveGysin_pairing
#print axioms CycleQ2LiteralAmbientMovingGysin.curveGysin_ne_zero

#print axioms CycleQ2LiteralAmbientMovingGysin.curveGysinVolume_pairing
