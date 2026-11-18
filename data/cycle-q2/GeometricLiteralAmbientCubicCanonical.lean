import Proposal.GeometricClosedEmbeddingCohomology
import Proposal.GeometricLiteralMovingResidueTrace
import Proposal.GeometricLiteralMovingCurveDifferential
import Proposal.GeometricLiteralSweptExtSupport
import Proposal.GeometricLiteralAmbientCubicSequence
import Proposal.GeometricLiteralAmbientCubicRatios
import Proposal.GeometricSurfaceCoordinateCubicFrames
import Proposal.GeometricSurfaceResidueFunctoriality

/-!
# Cubic adjunction on the embedded projective surface

The three residue frames on the original surface differ from the restrictions
of the ambient cubic frames by their projective orientation signs. Gluing the
three signed frame isomorphisms identifies the actual quotient in the ambient
Cartier sequence with the direct image of canonical two-forms.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAmbientCubicCanonical

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open CycleQ2GeometricModuleLocalIso CycleQ2LiteralAmbientCubicSequence
  CycleQ2HodgeAtlasLine CycleQ2HodgeThreefoldTwist CycleQ2GeometricHodgeThreefoldIncidence
open CycleQ2FullSurfaceJacobianCover (projectiveIndex)
open CycleQ2FullSurfaceResidueCover (coordinateOpen coordinateOpen_cover)
open CycleQ2SurfaceCoordinateFrames (Surface CanonicalForms coordinateExteriorFrame)
open CycleQ2SurfaceCoordinateCubicFrames (orientation orientation_mul_self coordinateExteriorFrame_transition)
open CycleQ2GeometricProjectiveCurve.Twisted (res)
open CycleQ2LiteralAmbientCubicRatios (model_surface_open surface_cubic_transition)

private abbrev cFrame (i : Fin 3) (V : Surface.Opens) (h : V ≤ coordinateOpen i) :
    Γ(CanonicalForms,V) ≃ₗ[Γ(Surface,V)] Γ(Surface,V) :=
  (coordinateExteriorFrame i).app V h

private abbrev tFrame (i : Fin 3) (V : Surface.Opens) (h : V ≤ coordinateOpen i) :=
  frame (pulled embedding (cocycle literalEval 3)) (projectiveIndex i) V
    (h.trans (model_surface_open i).ge)

private def sign (i : Fin 3) (V : Surface.Opens) : Γ(Surface,V)ˣ :=
  ⟨orientation i,orientation i,orientation_mul_self i V,orientation_mul_self i V⟩

private def chartIso (i : Fin 3) (V : Surface.Opens) (h : V ≤ coordinateOpen i) :
    Γ(restrictedO3,V) ≃ₗ[Γ(Surface,V)] Γ(CanonicalForms,V) :=
  (tFrame i V h).trans ((LinearEquiv.smulOfUnit (sign i V)).trans (cFrame i V h).symm)

private theorem chartIso_coeff (i : Fin 3) (V : Surface.Opens) (h : V ≤ coordinateOpen i)
    (s : Γ(restrictedO3,V)) :
    cFrame i V h (chartIso i V h s) = (orientation i : Γ(Surface,V)) * tFrame i V h s := by
  change cFrame i V h ((cFrame i V h).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  rfl

private def chartPatch (i : Fin 3) : PatchIso restrictedO3 CanonicalForms (coordinateOpen i) where
  app := chartIso i
  naturality {V W} hWV hV s := by
    apply (cFrame i W (hWV.trans hV)).injective
    have he := (coordinateExteriorFrame i).naturality hWV hV (chartIso i V hV s)
    change restrictRing (X := Surface) hWV (cFrame i V hV (chartIso i V hV s)) =
      cFrame i W (hWV.trans hV) (CanonicalForms.val.map (homOfLE hWV).op _) at he
    rw [← he, chartIso_coeff, chartIso_coeff, map_mul, map_intCast]
    exact congrArg ((orientation i : Γ(Surface,W)) * ·)
      (coordinate_restrict (pulled embedding (cocycle literalEval 3)) (projectiveIndex i)
        (hV.trans (model_surface_open i).ge) hWV s).symm

private theorem chartPatch_compatible (i j : Fin 3) : (chartPatch i).Compatible (chartPatch j) := by
  intro V hi hj s
  change chartIso i V hi s = chartIso j V hj s
  apply (cFrame i V hi).injective
  have ht := coordinate_transition (pulled embedding (cocycle literalEval 3)) (projectiveIndex i)
    (projectiveIndex j) V (hi.trans (model_surface_open i).ge) (hj.trans (model_surface_open j).ge) s
  change tFrame i V hi s = _ * tFrame j V hj s at ht
  rw [surface_cubic_transition i j V hi hj] at ht
  rw [chartIso_coeff, coordinateExteriorFrame_transition i j V hi hj, chartIso_coeff, ht]
  have hs := orientation_mul_self j V
  let z := CycleQ2SurfaceCoordinateSections.coordinatePolynomialSection 57 1 (projectiveIndex i)
    V hi (MvPolynomial.X (projectiveIndex j).castSucc) ^ 3
  change (orientation i : Γ(Surface,V)) * (z * tFrame j V hj s) =
    ((orientation i : Γ(Surface,V)) * (orientation j : Γ(Surface,V))) * z *
      ((orientation j : Γ(Surface,V)) * tFrame j V hj s)
  linear_combination - (orientation i : Γ(Surface,V)) * z * tFrame j V hj s * hs

/-- Adjunction identifies the literal restricted cubic line on D with its
canonical sheaf of Kähler two-forms. -/
def cubicCanonicalIso : restrictedO3 ≅ CanonicalForms := by
  let p := CycleQ2LocalFrameGluing.Cover.gluePatchIso restrictedO3 CanonicalForms ⊤ coordinateOpen
    coordinateOpen_cover.ge chartPatch chartPatch_compatible
  exact glueIso _ _ ⊤ ⊤ (by simp) p p (fun _ _ _ _ => rfl)

def directImageCanonicalIso : surfaceTwistOnFiber ≅
    (Scheme.Modules.pushforward CycleQ2LiteralAmbientSurface.surfaceToFiber).obj CanonicalForms :=
  (Scheme.Modules.pushforward _).mapIso cubicCanonicalIso

def canonicalSequence : ShortComplex T.Modules :=
  ShortComplex.mk incidenceSequence.f (incidenceSequence.g ≫ directImageCanonicalIso.hom)
    (by rw [← Category.assoc,incidenceSequence.zero,Limits.zero_comp])

theorem canonicalSequence_shortExact : canonicalSequence.ShortExact :=
  ShortComplex.shortExact_of_iso (ShortComplex.isoMk (Iso.refl _) (Iso.refl _) directImageCanonicalIso
    (by simp [canonicalSequence]) (by simp [canonicalSequence])) incidenceSequence_shortExact

private instance forgetZero : (SheafOfModules.toSheaf.{0} T.ringCatSheaf).PreservesZeroMorphisms :=
  CycleQ2LiteralSweptExtSupport.forgetPreservesZero T

abbrev additiveSequence := canonicalSequence.map (SheafOfModules.toSheaf.{0} T.ringCatSheaf)

theorem additiveSequence_shortExact : additiveSequence.ShortExact :=
  CycleQ2LiteralSweptExtSupport.additiveShortExact canonicalSequence_shortExact

local instance (Z : TopCat.{0}) : HasExt.{1} (Z.Sheaf AddCommGrpCat.{0}) := HasExt.standard _
local instance (Z : Scheme.{0}) : HasExt.{1} (Sheaf (Opens.grothendieckTopology Z) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Residue along the original cubic surface in the fixed threefold. -/
def surfaceConnecting (V : T.Opens) :
    (addSheaf ((Scheme.Modules.pushforward CycleQ2LiteralAmbientSurface.surfaceToFiber).obj
      CanonicalForms)).H' 2 V →+ (addSheaf (structureOn T)).H' 3 V :=
  CycleQ2GeometricIntrinsicCartierCohomology.openConnecting additiveSequence_shortExact 2 V

/-- Its kernel is exactly the image of the middle positive cubic twist. -/
theorem surfaceConnecting_eq_zero_iff (V : T.Opens) (c : additiveSequence.X₃.H' 2 V) :
    surfaceConnecting V c = 0 ↔ ∃ a : (addSheaf O3OnFiber).H' 2 V,
      a.comp (CategoryTheory.Abelian.Ext.mk₀ additiveSequence.g) (add_zero 2) = c := by
  constructor
  · exact fun h => CategoryTheory.Abelian.Ext.covariant_sequence_exact₃
      (CycleQ2InjectiveCech.freeOpen V) additiveSequence_shortExact c rfl h
  · rintro ⟨a,rfl⟩
    change (a.comp _ (add_zero 2)).comp additiveSequence_shortExact.extClass rfl = 0
    simp only [CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero,
      ShortComplex.ShortExact.comp_extClass, CategoryTheory.Abelian.Ext.comp_zero]

open CycleQ2LiteralMovingResidueClass CycleQ2LiteralMovingResidueExact
  CycleQ2LiteralAbelJacobiMovingFaces CycleQ2SeedSectionAffineInjective
  CycleQ2LiteralCotangentTrace CycleQ2ClosedEmbeddingCohomology

local instance : IsClosedImmersion CycleQ2LiteralAmbientSurface.surfaceToFiber :=
  CycleQ2LiteralAmbientSurface.surfaceToFiber_isClosedImmersion

/-- The moving residue class, computed on the original embedded surface, as a
degree-two class on the threefold with coefficients supported on that surface. -/
def movingSurfaceClass (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) : additiveSequence.X₃.H' 2 ⊤ :=
  pushHEquiv CycleQ2LiteralAmbientSurface.surfaceToFiber.base
    CycleQ2LiteralAmbientSurface.surfaceToFiber.isClosedEmbedding (addSheaf CanonicalForms) 2
    (residueConnecting t ht ⊤ (residueClass t ht pivotOne pivotOne_closed))

theorem movingSurfaceClass_ne_zero (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    movingSurfaceClass t ht ≠ 0 := by
  intro h
  apply CycleQ2LiteralMovingResidueTrace.residueConnecting_trace_ne_zero t ht
  have he := (pushHEquiv CycleQ2LiteralAmbientSurface.surfaceToFiber.base
    CycleQ2LiteralAmbientSurface.surfaceToFiber.isClosedEmbedding (addSheaf CanonicalForms) 2).injective
  have hz : residueConnecting t ht ⊤ (residueClass t ht pivotOne pivotOne_closed) = 0 :=
    he (by simpa only [map_zero] using h)
  rw [hz,map_zero]

/-- Nonvanishing of the original double boundary follows from vanishing of
the degree-two cohomology of the actual ambient positive twist. -/
theorem movingSurfaceConnecting_ne_zero (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (h₃ : Subsingleton ((addSheaf O3).H' 2 ⊤)) :
    surfaceConnecting ⊤ (movingSurfaceClass t ht) ≠ 0 := by
  intro h
  obtain ⟨a,ha⟩ := (surfaceConnecting_eq_zero_iff _ _).mp h
  let e : (addSheaf O3).H' 2 ⊤ ≃+ (addSheaf O3OnFiber).H' 2 ⊤ :=
    pushHEquiv literalIso.hom.base literalIso.hom.isClosedEmbedding (addSheaf O3) 2
  have ha0 : a = 0 := e.symm.injective (h₃.allEq _ _)
  rw [ha0, CategoryTheory.Abelian.Ext.zero_comp] at ha
  exact movingSurfaceClass_ne_zero t ht ha.symm

open CategoryTheory.Abelian CycleQ2SeedSectionSheafCurveBinding CycleQ2LiteralMovingResidueCurve
  CycleQ2LiteralMovingResidueDifferentialClass CycleQ2LiteralMovingCurveDifferentialNonzero

/-- Both successive residue maps on the genuine function-valued two-stage
Cartier cohomology of Γ ⊂ D ⊂ T. -/
def iteratedResidue (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    (curveForms t).H' 1 ⊤ →+ (addSheaf (structureOn T)).H' 3 ⊤ :=
  (surfaceConnecting ⊤).comp <|
    (pushHEquiv CycleQ2LiteralAmbientSurface.surfaceToFiber.base
      CycleQ2LiteralAmbientSurface.surfaceToFiber.isClosedEmbedding (addSheaf CanonicalForms) 2).toAddMonoidHom.comp <|
    (residueConnecting t ht ⊤).comp <|
    ((Ext.mk₀ (curveResidue t ht)).postcomp _ (add_zero 1)).comp
      (pushHEquiv (curveToSurface t).base (curveToSurface t).isClosedEmbedding (curveForms t) 1).toAddMonoidHom

theorem iteratedResidue_curveClass (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    iteratedResidue t ht (curveClass t) = surfaceConnecting ⊤ (movingSurfaceClass t ht) := by
  exact congrArg (fun x => surfaceConnecting ⊤
    (pushHEquiv CycleQ2LiteralAmbientSurface.surfaceToFiber.base
      CycleQ2LiteralAmbientSurface.surfaceToFiber.isClosedEmbedding (addSheaf CanonicalForms) 2
      (residueConnecting t ht ⊤ x))) (curveClass_residue t ht)

end CycleQ2LiteralAmbientCubicCanonical
end

#print axioms CycleQ2LiteralAmbientCubicCanonical.cubicCanonicalIso
#print axioms CycleQ2LiteralAmbientCubicCanonical.directImageCanonicalIso
#print axioms CycleQ2LiteralAmbientCubicCanonical.surfaceConnecting_eq_zero_iff
#print axioms CycleQ2LiteralAmbientCubicCanonical.movingSurfaceConnecting_ne_zero
#print axioms CycleQ2LiteralAmbientCubicCanonical.iteratedResidue_curveClass
