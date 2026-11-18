import Proposal.GeometricLiteralMovingCurveTraceLinearity
import Proposal.GeometricLiteralMovingCurveTraceIsomorphism
import Proposal.GeometricLiteralMovingCurveConnected

/-!
# The algebraic trace line of the connected moving curve

The normalized adjunction residue identifies the first cohomology of
curve differentials with the complex numbers. Multiplication by a global
regular function acts on this line by its complex constant. Every
complex-linear trace isomorphism is a nonzero multiple of the
normalized one.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralMovingCurveDuality
open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace Opposite
  CycleQ2SeedSectionAffineInjective CycleQ2SeedSectionSheafCurveBinding
  CycleQ2LiteralMovingCurveTraceLinearity CycleQ2LiteralMovingCurveTraceIsomorphism
  CycleQ2LiteralMovingCurveDifferentialNonzero CycleQ2LiteralMovingCurveConnected
  CycleQ2LiteralMovingResidueCurve CycleQ2GeometricSheafCohomologyScalar
open CycleQ2LiteralMovingResidueAdjunction.AffineFrame (curveCoefficient)

local instance (T : TopCat.{0}) : HasExt.{1} (T.Sheaf AddCommGrpCat.{0}) := HasExt.standard _
local instance (X : Scheme.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) (hi : AlgebraicIndependent ℚ t)

def traceEquiv : (curveForms t).H' 1 ⊤ ≃ₗ[ℂ] ℂ :=
  LinearEquiv.ofBijective (differentialTraceLinear t ht) (differentialTraceEquiv t ht hi).bijective

theorem traceEquiv_apply (x : (curveForms t).H' 1 ⊤) : traceEquiv t ht hi x = differentialTrace t ht x := rfl

theorem function_eq_coefficient (c : ℂ) : movingFunctionsEquiv t ht c = curveCoefficient t c := by
  change (curveToSurface t).appTop (CycleQ2GeometricSurfaceCoefficients.projectiveGlobalCoefficient 57 1 c) = _
  exact (CycleQ2GeometricAffineChartSections.schemeCoefficient_comp (curveToSurface t)
    (CycleQ2GeometricSurfaceCoefficients.projectiveToComplex 57 1) c).symm

def functionEnd (g : Γ(Curve t,⊤)) : curveForms t ⟶ curveForms t :=
  scalarEnd (Curve t).sheaf (curveCoefficient t) (curveDifferentials t) ((movingFunctionsEquiv t ht).symm g)

theorem functionEnd_apply (g : Γ(Curve t,⊤)) (U : (Curve t).Opens) (s : (curveDifferentials t).val.obj (op U)) :
    (functionEnd t ht g).hom.app (op U) s =
      (Curve t).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op g • s := by
  change (Curve t).presheaf.map (homOfLE (le_top : U ≤ ⊤)).op
    (curveCoefficient t ((movingFunctionsEquiv t ht).symm g)) • s = _
  rw [← function_eq_coefficient t ht, RingEquiv.apply_symm_apply]

theorem trace_function (g : Γ(Curve t,⊤)) (x : (curveForms t).H' 1 ⊤) :
    differentialTrace t ht (x.comp (Ext.mk₀ (functionEnd t ht g)) (add_zero 1)) =
      (movingFunctionsEquiv t ht).symm g * differentialTrace t ht x :=
  differentialTrace_smul t ht _ x

theorem any_trace_is_unit_multiple (T : (curveForms t).H' 1 ⊤ ≃ₗ[ℂ] ℂ) :
    ∃ u : ℂˣ, ∀ x, T x = (u : ℂ) * differentialTrace t ht x := by
  let e := traceEquiv t ht hi
  let a := e.symm 1
  have h₁ : e a = 1 := e.apply_symm_apply 1
  have hT : T a ≠ 0 := by
    intro hz
    have ha : a = 0 := T.injective (hz.trans T.map_zero.symm)
    exact one_ne_zero (h₁.symm.trans (ha ▸ e.map_zero))
  refine ⟨Units.mk0 _ hT, fun x => ?_⟩
  have hx : (e x) • a = x := by
    apply e.injective
    rw [map_smul, h₁, smul_eq_mul, mul_one]
  calc
    T x = T ((e x) • a) := congrArg T hx.symm
    _ = (e x) * T a := T.map_smul _ _
    _ = _ := mul_comm _ _

theorem any_trace_curveClass_ne_zero (T : (curveForms t).H' 1 ⊤ ≃ₗ[ℂ] ℂ) :
    T (curveClass t) ≠ 0 := by
  obtain ⟨u,hu⟩ := any_trace_is_unit_multiple t ht hi T
  rw [hu]
  exact mul_ne_zero u.ne_zero (differentialTrace_curveClass_ne_zero t ht)

end CycleQ2LiteralMovingCurveDuality
end

#print axioms CycleQ2LiteralMovingCurveDuality.traceEquiv
#print axioms CycleQ2LiteralMovingCurveDuality.any_trace_curveClass_ne_zero
