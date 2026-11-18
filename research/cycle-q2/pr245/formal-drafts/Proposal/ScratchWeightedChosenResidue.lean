import Proposal.ScratchWeightedGenericPointMap
import Proposal.WeightedConeVertex
import Proposal.GeometricLogarithmicChartDerivative

/-! The regular representative of the selected residue, in the actual
structure sections of the native affine open, evaluates to the field
three-form whose coefficient occurs in the original primitive identity. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2.Cech.Sections CycleQ2WeightedResidueAtlas CycleQ2WeightedIntersectionFrame
  CycleQ2GeometricHodgeThreefold CycleQ2HodgeEuler CycleQ2HodgeEulerChartDerivations
  CycleQ2HodgeEulerContractionCharts CycleQ2WeightedGenericPointMap
  CycleQ2WeightedConeUniversal
open CycleQ2WeightedConeVertex (grad GradientRing residueSection coneNumerator evalSection chart_density)
open CycleQ2LogarithmicPullback (Forms exactWedge pull_exactWedge)
open CycleQ2LogarithmicChartDerivative (pull)
open scoped CycleQ2WeightedConeUniversal
namespace CycleQ2WeightedChosenResidue
abbrev T := threefold coefficients
abbrev V := U coefficients chosen
abbrev A := Γ(T,V)
local instance : Algebra Base A := algebra (toBase coefficients) V

def chartValue : Poly Base →ₐ[Base] A :=
  (coordinateEquiv coefficients chosen).toAlgHom.comp
    ((patchMap affineEquation 0).comp (mk affineEquation))

def coneValue := chartValue.comp (dehom (R := Base) (0 : Fin 4))

theorem native_normal_unit : IsUnit (coneValue (grad 1 (equation coefficients))) := by
  have h : dehom (R:=Base) 0 (pderiv (1 : Fin 5) (equation coefficients)) =
      pderiv (0 : Fin 4) affineEquation :=
    (pderiv_dehom (0 : Fin 4) (0 : Fin 4) (equation coefficients)).symm
  change IsUnit (chartValue (dehom 0 (pderiv 1 (equation coefficients))))
  rw [h]
  exact (IsLocalization.Away.algebraMap_isUnit (S:=Model coefficients chosen)
    (gradientEntry affineEquation 0)).map (coordinateEquiv coefficients chosen).toMonoidHom

def regularEval : GradientRing 1 (equation coefficients) →+* A :=
  IsLocalization.Away.lift (grad 1 (equation coefficients)) (f:=coneValue.toRingHom) native_normal_unit

def coefficient : A := regularEval (residueSection 1 (equation coefficients) (coneNumerator Base))
def coordinate (j : Fin 3) : A := chartValue (X j.succ)
def form : Forms Base A 3 := coefficient • exactWedge (k:=Base) 3 coordinate

theorem fieldCoefficient : genericPoint coefficient =
    CycleQ2MonicWeightedPrimitiveIdentity.density value affineEquation := by
  have h : genericPoint.toRingHom.comp regularEval =
      evalSection 1 (equation coefficients) (value.comp (dehom 0).toRingHom) generic_normal := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (grad 1 (equation coefficients)))
    apply RingHom.ext
    intro p
    change genericPoint (regularEval (algebraMap _ _ p)) = evalSection _ _ _ _ (algebraMap _ _ p)
    rw [show regularEval (algebraMap _ _ p) = coneValue p from IsLocalization.Away.lift_eq _ _ _,
      show evalSection _ _ _ _ (algebraMap _ _ p) = value (dehom 0 p) from
        IsLocalization.Away.lift_eq _ _ _]
    exact genericPoint_coordinate (dehom 0 p)
  exact (RingHom.congr_fun h (residueSection 1 (equation coefficients) (coneNumerator Base))).trans
    (chart_density coefficients value generic_normal)

theorem genericPoint_coordinate' (j : Fin 3) : genericPoint (coordinate j) = spatial j :=
  (genericPoint_coordinate (X j.succ)).trans (eval₂Hom_X' _ _ _)

theorem genericPoint_form : pull genericPoint 3 form = topForm := by
  rw [form, map_smulₛₗ,fieldCoefficient,pull_exactWedge]
  unfold topForm CycleQ2GenericWeightedExterior.volume exactWedge
  congr 2
  funext i
  rw [Function.comp_apply,genericPoint_coordinate',coordinateBasis_apply]

end CycleQ2WeightedChosenResidue
end
#print axioms CycleQ2WeightedChosenResidue.genericPoint_form
