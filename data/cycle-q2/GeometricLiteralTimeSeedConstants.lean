import Proposal.GeometricCurveDeRhamOne
import Proposal.GeometricProperGlobalFunctions
import Proposal.GeometricLiteralTimeSeedComponent
import Proposal.GeometricLiteralTimeCurveReduced

/-!
# Constants on the proper time component through the fixed seed

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeSeedConstants

open AlgebraicGeometry CategoryTheory Opposite CycleQ2LiteralTimeSeedComponent
  CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialSheaf
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2IncidenceSeedFiberCover (seedBasePoint)

variable (V : parameterScheme.Opens) (hV : seedBasePoint ∈ V)

/-- Every regular function on the marked proper component is a complex scalar. -/
theorem globalFunctions_constant : Function.Surjective (schemeCoefficient (componentStructure V hV)) := by
  have : AlgebraicGeometry.IsReduced (Component V hV) := componentReduced V hV
  exact CycleQ2ProperGlobalFunctions.schemeCoefficient_surjective (componentStructure V hV)

private theorem differential_zero_of_constants (X : Scheme.{0}) (c : ℂ →+* Γ(X, ⊤))
    (hc : Function.Surjective c) (s : Γ(X, ⊤)) :
    (universalDifferential X.sheaf c).d (X := op ⊤) s = 0 := by
  obtain ⟨z, rfl⟩ := hc s
  have hz : coefficientOn X.sheaf c ⊤ z = c z :=
    ConcreteCategory.congr_hom (X.presheaf.map_id (op ⊤)) _
  exact (congrArg ((universalDifferential X.sheaf c).d (X := op ⊤)) hz.symm).trans
    ((universalDifferential X.sheaf c).d_app (X := op ⊤) z)

/-- The genuine sheaf-valued Kähler differential kills every global function on
the proper component containing the seed and its marked tangent. -/
theorem globalFunction_differential_zero (s : Γ(Component V hV, ⊤)) :
    (universalDifferential (Component V hV).sheaf
      (schemeCoefficient (componentStructure V hV))).d (X := op ⊤) s = 0 :=
  differential_zero_of_constants (Component V hV) (schemeCoefficient (componentStructure V hV))
    (globalFunctions_constant V hV) s

/-- A nonzero global one-form on the actual proper component has nonzero
class in its two-term de Rham complex. -/
theorem formClass_ne_zero
    (ω : CycleQ2InjectiveCech.Sections (CycleQ2CurveDeRhamOne.OneForms (Component V hV)
      (schemeCoefficient (componentStructure V hV))) ⊤) (hω : ω ≠ 0) :
    CycleQ2CurveDeRhamOne.formClass (Component V hV)
      (schemeCoefficient (componentStructure V hV)) ω ≠ 0 :=
  CycleQ2CurveDeRhamOne.formClass_ne_zero_of_constants (Component V hV)
    (schemeCoefficient (componentStructure V hV)) (globalFunctions_constant V hV) ω hω

end CycleQ2LiteralTimeSeedConstants

#print axioms CycleQ2LiteralTimeSeedConstants.globalFunctions_constant
#print axioms CycleQ2LiteralTimeSeedConstants.globalFunction_differential_zero
#print axioms CycleQ2LiteralTimeSeedConstants.formClass_ne_zero
