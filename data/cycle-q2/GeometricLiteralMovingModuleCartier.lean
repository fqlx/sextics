import Proposal.GeometricClosedEmbeddingCohomology
import Proposal.GeometricLiteralAmbientSurface
import Proposal.GeometricLiteralSweptExtSupport
import Proposal.GeometricLiteralMovingResidueExact

/-!
# The module Cartier extension of the moving divisor

On the original surface, the regular-to-pole morphism is linear over the
structure sheaf. Its cokernel in sheaves of modules has the same additive
residue extension and connecting map as the moving curve calculation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingModuleCartier

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace
open CycleQ2SurfaceCoordinateFrames (Surface CanonicalForms)
open CycleQ2LiteralMovingResidueExact
open CycleQ2LiteralMovingResiduePole (PoleForms)
open CycleQ2SeedSectionSheafCurveBinding (curveToSurface)
open CycleQ2SeedSectionAffineInjective (ChartRegular)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2GeometricIntrinsicNormal CycleQ2LocalHomFrame
attribute [local instance] CycleQ2GeometricIntrinsicNormal.overHomCommModuleMk
  CycleQ2GeometricIntrinsicNormal.localLinearRingModule CycleQ2GeometricIntrinsicNormal.moduleHomObjModule
attribute [local instance] CycleQ2LiteralSweptExtSupport.forgetFiniteColimits

abbrev forgetModules := SheafOfModules.toSheaf.{0} Surface.ringCatSheaf
local instance forgetZero : forgetModules.PreservesZeroMorphisms :=
  CycleQ2LiteralSweptExtSupport.forgetPreservesZero Surface

abbrev inclusion (t : Fin 3 → ℂ) : CanonicalForms ⟶ PoleForms t :=
  idealRegularInclusion (curveToSurface t) CanonicalForms
abbrev quotient (t : Fin 3 → ℂ) : Surface.Modules := cokernel (inclusion t)

def sequence (t : Fin 3 → ℂ) : ShortComplex Surface.Modules :=
  ShortComplex.mk (inclusion t) (cokernel.π _) (cokernel.condition _)

theorem shortExact (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) : (sequence t).ShortExact where
  mono_f := forgetModules.mono_of_mono_map (regular_mono t ht)
  epi_g := inferInstanceAs (Epi (cokernel.π (inclusion t)))
  exact := ShortComplex.exact_cokernel _

def quotientAddIso (t : Fin 3 → ℂ) : addSheaf (quotient t) ≅ residueQuotient t :=
  PreservesCokernel.iso forgetModules (inclusion t)

theorem projection_quotientAddIso (t : Fin 3 → ℂ) :
    forgetModules.map (cokernel.π (inclusion t)) ≫ (quotientAddIso t).hom =
      cokernel.π (regularInclusion t) :=
  PreservesCokernel.π_iso_hom forgetModules (inclusion t)

abbrev ambientSurface := CycleQ2LiteralAmbientSurface.surfaceToFiber
abbrev onThreefold (t : Fin 3 → ℂ) := (sequence t).map (Scheme.Modules.pushforward ambientSurface)

local instance : IsClosedImmersion ambientSurface :=
  CycleQ2LiteralAmbientSurface.surfaceToFiber_isClosedImmersion

/-- Direct image of the moving module residue row on the original threefold.
The closed embedding gives exact additive direct image, and the forgetful
functor reflects short exactness. -/
theorem onThreefold_shortExact (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    (onThreefold t).ShortExact := by
  apply CategoryTheory.ShortExact.reflects_shortExact_of_faithful
    (SheafOfModules.toSheaf.{0} (CycleQ2LiteralAmbientSmooth.IncidenceFiber 57).ringCatSheaf)
  exact CycleQ2ClosedEmbeddingCohomology.pushShortExact ambientSurface.base ambientSurface.isClosedEmbedding
    (CycleQ2LiteralSweptExtSupport.additiveShortExact (shortExact t ht))

end CycleQ2LiteralMovingModuleCartier
end

#print axioms CycleQ2LiteralMovingModuleCartier.shortExact
#print axioms CycleQ2LiteralMovingModuleCartier.onThreefold_shortExact
