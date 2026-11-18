import Proposal.GeometricLiteralMovingModuleResidue
import Proposal.GeometricLiteralMovingCurveDifferentialNonzero
import Proposal.GeometricCanonicalResidueScalar

/-!
# Complex linearity of the intrinsic moving curve trace

The scalar action is induced from the original module of curve
differentials. The closed immersion respects constants, the actual
residue is a module morphism, and its boundary commutes with scalar
multiplication on the Cartier extension.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option maxRecDepth 3500
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralMovingCurveTraceLinearity

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2ClosedEmbeddingCohomology CycleQ2ClosedEmbeddingSheafExact CycleQ2ClosedEmbeddingSheafDescent
  CycleQ2SeedSectionAffineInjective CycleQ2SeedSectionSheafCurveBinding
  CycleQ2LiteralMovingResiduePole CycleQ2LiteralMovingResidueCurve CycleQ2LiteralMovingResidueExact
  CycleQ2LiteralMovingModuleCartier CycleQ2LiteralMovingModuleResidue CycleQ2LiteralMovingQuotientTrace
  CycleQ2LiteralMovingCurveDifferentialNonzero CycleQ2LiteralCotangentTrace
  CycleQ2GeometricSheafCohomologyScalar CycleQ2GeometricIntrinsicCartierCohomology
open CycleQ2SurfaceCoordinateFrames (Surface CanonicalForms)
open CycleQ2LiteralNativeDifferentialSections (globalCoefficient)
open CycleQ2LiteralMovingResidueAdjunction.AffineFrame (curveCoefficient curveMap_constants)

local instance (T : TopCat.{0}) : HasExt.{1} (T.Sheaf AddCommGrpCat.{0}) := HasExt.standard _
local instance (T : TopCat.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance (X : Scheme.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

instance curveCohomologyModule : Module ℂ ((curveForms t).H' 1 ⊤) :=
  cohomologyModule (Curve t).sheaf (curveCoefficient t) (curveDifferentials t) 1 ⊤

private abbrev scalar (M : Surface.Modules) (z : ℂ) := scalarEnd Surface.sheaf globalCoefficient M z
private abbrev onCurve (z : ℂ) := scalarEnd (Curve t).sheaf (curveCoefficient t) (curveDifferentials t) z
private abbrev onQuotient (z : ℂ) := (quotientAddIso t).inv ≫ scalar (quotient t) z ≫ (quotientAddIso t).hom

theorem push_scalar (z : ℂ) :
    (push (curveToSurface t).base).map (onCurve t z) = scalar (curveModule t) z := by
  ext W x
  exact congrArg (fun c : Γ(Curve t,(curveToSurface t) ⁻¹ᵁ W.unop) => c • x)
    (curveMap_constants (W := W.unop) t z).symm

private def scalarDiagram (z : ℂ) : residueComplex t ⟶ residueComplex t where
  τ₁ := scalar CanonicalForms z
  τ₂ := scalar (PoleForms t) z
  τ₃ := onQuotient t z
  comm₁₂ := scalarEnd_naturality Surface.sheaf globalCoefficient CanonicalForms (inclusion t) z
  comm₂₃ := by
    change scalar (PoleForms t) z ≫ cokernel.π (regularInclusion t) =
      cokernel.π (regularInclusion t) ≫ onQuotient t z
    rw [← projection_quotientAddIso]
    unfold onQuotient
    simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc, scalarEnd_naturality Surface.sheaf globalCoefficient (PoleForms t) (cokernel.π (inclusion t)) z,
      Category.assoc]

private theorem curveResidue_scalar (z : ℂ) :
    (push (curveToSurface t).base).map (onCurve t z) ≫ curveResidue t ht =
      curveResidue t ht ≫ onQuotient t z := by
  rw [push_scalar, ← moduleResidue_additive]
  unfold onQuotient
  simp only [Category.assoc, Iso.hom_inv_id_assoc]
  rw [← Category.assoc, scalarEnd_naturality Surface.sheaf globalCoefficient (curveModule t) (moduleResidue t ht) z,
    Category.assoc]

theorem differentialTrace_smul (z : ℂ) (x : (curveForms t).H' 1 ⊤) :
    differentialTrace t ht (z • x) = z • differentialTrace t ht x := by
  let e := pushHEquiv (curveToSurface t).base (curveToSurface t).isClosedEmbedding (curveForms t) 1
  let r := curveResidue t ht
  let y := (e x).comp (Ext.mk₀ r) (add_zero 1)
  have hpush : e (z • x) = (e x).comp (Ext.mk₀ ((push (curveToSurface t).base).map (onCurve t z))) (add_zero 1) :=
    pushHEquiv_natural (curveToSurface t).base (curveToSurface t).isClosedEmbedding (onCurve t z) 1 x
  have hm : (e (z • x)).comp (Ext.mk₀ r) (add_zero 1) = y.comp (Ext.mk₀ (onQuotient t z)) (add_zero 1) := by
    dsimp only [y]
    rw [hpush, Ext.comp_assoc_of_third_deg_zero, Ext.comp_assoc_of_third_deg_zero,
      Ext.mk₀_comp_mk₀, Ext.mk₀_comp_mk₀, curveResidue_scalar]
  have hδ : residueConnecting t ht ⊤ (y.comp (Ext.mk₀ (onQuotient t z)) (add_zero 1)) =
      z • residueConnecting t ht ⊤ y :=
    openConnecting_naturality (residueShortExact t ht) (residueShortExact t ht) (scalarDiagram t z) 1 ⊤ y
  change algebraicTrace (residueConnecting t ht ⊤ ((e (z • x)).comp (Ext.mk₀ r) _)) =
    z • algebraicTrace (residueConnecting t ht ⊤ y)
  rw [hm, hδ, map_smul]

def differentialTraceLinear : (curveForms t).H' 1 ⊤ →ₗ[ℂ] ℂ where
  __ := differentialTrace t ht
  map_smul' := differentialTrace_smul t ht

end CycleQ2LiteralMovingCurveTraceLinearity
end

#print axioms CycleQ2LiteralMovingCurveTraceLinearity.differentialTraceLinear
