import Proposal.GeometricLiteralMovingCurveTraceSurjective
import Proposal.GeometricLiteralMovingPoleTwistVanishing

/-!
# The adjunction residue trace of the marked moving curve

Vanishing of the first cohomology of the sheaf of surface two-forms
with a pole on the curve makes the residue trace injective. Together
with surjectivity this identifies the first cohomology of the actual
curve's sheaf of differential forms with the additive group of complex
numbers.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralMovingCurveTraceIsomorphism

open CategoryTheory AlgebraicGeometry TopologicalSpace
  CycleQ2SeedSectionAffineInjective CycleQ2LiteralMovingResidueCurve
  CycleQ2LiteralMovingCurveDifferentialNonzero
  CycleQ2LiteralMovingCurveTraceSurjective CycleQ2LiteralMovingPoleTwistVanishing

local instance (T : TopCat.{0}) : HasExt.{1} (T.Sheaf AddCommGrpCat.{0}) := HasExt.standard _
local instance (T : TopCat.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _
local instance (X : Scheme.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) (hi : AlgebraicIndependent ℚ t)

def differentialTraceEquiv : (curveForms t).H' 1 ⊤ ≃+ ℂ :=
  differentialTraceEquivOfVanishing t ht hi (poleHOne t ht)

theorem differentialTraceEquiv_apply (x : (curveForms t).H' 1 ⊤) :
    differentialTraceEquiv t ht hi x = differentialTrace t ht x := rfl

theorem differentialTraceEquiv_curveClass_ne_zero :
    differentialTraceEquiv t ht hi (curveClass t) ≠ 0 :=
  differentialTrace_curveClass_ne_zero t ht

end CycleQ2LiteralMovingCurveTraceIsomorphism
end

#print axioms CycleQ2LiteralMovingCurveTraceIsomorphism.differentialTraceEquiv
