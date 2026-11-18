import Proposal.ScratchWeightedNativeCech
import Proposal.ScratchWeightedGenericPointMap
import Mathlib.Tactic.FinCases

/-! # Restriction of the complete weighted Čech class to the literal rational de Rham quotient

The differential on differential forms computed in the native gradient atlas
agrees after field restriction with the three-coordinate `d₂` of the universal
moving threefold. Both are standard exterior differentiation on a·db∧dc. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

open AlgebraicGeometry CycleQ2.Cech CycleQ2CechDeRhamTotalThree
open CycleQ2WeightedResidueAtlas CycleQ2GeometricHodgeThreefold
open CycleQ2WeightedGenericPointMap CycleQ2WeightedConeUniversal
open scoped CycleQ2WeightedConeUniversal
open CycleQ2LogarithmicDifferential (exteriorD)
open CycleQ2LogarithmicChartDerivative (pull pull_d exact_symbol)
open CycleQ2LogarithmicPullback (exactWedge exact_generators)
namespace CycleQ2WeightedNativeCech

theorem field_derivative (ω : CycleQ2LogarithmicPullback.Forms Base FunctionField 2) :
    exteriorD coordinateBasis 2 ω = d₂ ω := by
  apply exact_generators coordinateBasis spatial coordinateBasis_apply 2
    (exteriorD coordinateBasis 2) d₂.toAddMonoidHom _ ω
  intro a t
  change exteriorD coordinateBasis 2 (a • exactWedge (k:=Base) 2 t) =
    d₂ (a • exactWedge (k:=Base) 2 t)
  rw [exact_symbol coordinateBasis spatial coordinateBasis_apply]
  have ht : t = ![t 0,t 1] := by funext i; fin_cases i <;> rfl
  have hcons : Fin.cons a t = ![a,t 0,t 1] := by funext i; fin_cases i <;> rfl
  rw [hcons,ht]
  simpa only [exactWedge] using (d₂_scalar_wedge a (t 0) (t 1)).symm

private abbrev chart := U coefficients chosen
private abbrev P := Native.P (toBase coefficients)
private abbrev vertexThree := (double coefficients).X 0 3

/-- The class of the explicitly evaluated vertex form in the three-coordinate
field quotient used by the primitive-existence theorem. -/
def evaluateVertex : vertexThree →+ TopDeRham :=
  (Submodule.mkQ (LinearMap.range d₂)).toAddMonoidHom.comp
    ((pull genericPoint 3).toAddMonoidHom.comp (vertex (U coefficients) (P 3) chosen).hom)

theorem evaluateVertex_d (a : (double coefficients).X 0 2) :
    evaluateVertex ((double coefficients).v 0 2 a) = 0 := by
  letI := Sections.algebra (toBase coefficients) chart
  obtain ⟨x,b,hx⟩ := CycleQ2WeightedIntersectionFrame.exact_frame coefficients chosen
    (affine coefficients chosen) (le_refl _)
  apply (Submodule.Quotient.mk_eq_zero _).mpr
  refine ⟨pull genericPoint 2 (vertex (U coefficients) (P 2) chosen a),?_⟩
  rw [← field_derivative,pull_d genericPoint b x hx coordinateBasis spatial coordinateBasis_apply,
    ← Native.vertex_d (toBase coefficients) (U coefficients) (frames coefficients) chosen b x hx 2]

/-- Restriction of the full Čech cohomology class to the literal function-field
de Rham quotient. -/
def toFunctionField : HThree coefficients →+ TopDeRham :=
  vertexMap _ evaluateVertex evaluateVertex_d

theorem toFunctionField_classOf (z : Cycles (double coefficients)) :
    toFunctionField (classOf _ z) = evaluateVertex z.1.1 := rfl

/-- A vanishing Čech class whose evaluated vertex is the universal source class
produces the requested actual primitive. -/
theorem primitive_of_total_zero (z : Cycles (double coefficients))
    (hz : classOf _ z = 0) (heval : evaluateVertex z.1.1 = sourceClass) :
    CycleQ2UniversalWeightedTransfer.UniversalWeightedPrimitiveExists := by
  apply class_zero_iff_primitive.mp
  rw [← heval,← toFunctionField_classOf,hz,map_zero]

end CycleQ2WeightedNativeCech
end
#print axioms CycleQ2WeightedNativeCech.field_derivative
#print axioms CycleQ2WeightedNativeCech.primitive_of_total_zero
