import Proposal.GeometricHodgeTopTraceScalars
import Proposal.GeometricLiteralThreefoldTopTraceTransport

/-!
# The complex-linear canonical trace of the fixed sextic threefold

The structural complex action on the monic model is the one pulled back along
the literal isomorphism. Composing its Laurent trace with inverse canonical
volume transport gives a linear equivalence on all of canonical top cohomology.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldCanonicalTraceLinear

open CategoryTheory AlgebraicGeometry TopologicalSpace
open CycleQ2GeometricHodgeThreefold (threefold toBase)
open CycleQ2GeometricHodgeThreefoldIncidence (literalEval literalIso literalIso_overComplex literal_vertex_unit)
open CycleQ2GeometricAffineChartSections (schemeCoefficient)
open CycleQ2GeometricSheafCohomologyScalar (cohomologyModule cohomologyScalar)
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2LiteralThreefoldCanonicalVolume (coeff threeForms structural)
open CycleQ2LiteralThreefoldHodgeCech (Threefold)
open CycleQ2LiteralThreefoldTopTrace (canonicalTrace toCanonical canonicalTrace_representative)
open CycleQ2LiteralThreefoldTopTraceTransport (sourceCoeff unitModule toCanonicalLinearEquiv)
open CycleQ2HodgeTopTraceScalars (structureTraceLinear)

local instance : HasExt.{1} (CycleQ2InjectiveCech.AbSheaf (show TopCat from Threefold)) := HasExt.standard _
local instance : HasExt.{1} (CycleQ2InjectiveCech.AbSheaf (show TopCat from threefold literalEval)) := HasExt.standard _
local instance : Module ℂ ((structureAdditiveSheaf (threefold literalEval)).H' 3 ⊤) :=
  cohomologyModule (threefold literalEval).sheaf sourceCoeff (unitModule (threefold literalEval)) 3 ⊤
local instance : Module ℂ ((addSheaf threeForms).H' 3 ⊤) := cohomologyModule Threefold.sheaf coeff threeForms 3 ⊤

theorem literal_transport_coefficient :
    schemeCoefficient (literalIso.hom ≫ structural) = sourceCoeff :=
  congrArg schemeCoefficient literalIso_overComplex

/-- The normalized Laurent trace on the geometric complex module of three-forms. -/
def canonicalTraceLinear : (addSheaf threeForms).H' 3 ⊤ ≃ₗ[ℂ] ℂ :=
  toCanonicalLinearEquiv.symm.trans (structureTraceLinear literalEval literal_vertex_unit)

theorem canonicalTraceLinear_apply (x : (addSheaf threeForms).H' 3 ⊤) :
    canonicalTraceLinear x = canonicalTrace x := rfl

theorem canonicalTrace_scalar (c : ℂ) (x : (addSheaf threeForms).H' 3 ⊤) :
    canonicalTrace (cohomologyScalar Threefold.sheaf coeff threeForms 3 ⊤ c x) = c * canonicalTrace x :=
  canonicalTraceLinear.map_smul c x

theorem canonicalTraceLinear_representative (a : ℂ) :
    canonicalTraceLinear (toCanonical (CycleQ2HodgeFourOpenStructureHThree.tripleConnecting
      literalEval literal_vertex_unit (CycleQ2HodgeDerivedTopTrace.representative
        (CycleQ2HodgeTwistTorusChart.structureLaurentSections literalEval literal_vertex_unit) a))) = a :=
  canonicalTrace_representative a

end CycleQ2LiteralThreefoldCanonicalTraceLinear

#print axioms CycleQ2LiteralThreefoldCanonicalTraceLinear.canonicalTraceLinear
#print axioms CycleQ2LiteralThreefoldCanonicalTraceLinear.canonicalTraceLinear_representative
