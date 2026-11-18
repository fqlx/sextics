import Proposal.GeometricWeightedAffineChartJets
import Proposal.GeometricHodgeThreefold
import Mathlib.RingTheory.Localization.FractionRing

/-! The universal monic family over the actual fraction field of its parameter
ring is represented by an explicit specialization of the original invariant
sextic. Its native first coordinate chart is obtained by coefficient extension
from the original polynomial family. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedConeUniversal

open MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing universalF)
open CycleQ2IncidenceNormalForm
open CycleQ2MonicWeightedAffineEquation (Coeff chart)

abbrev Base := FractionRing Coeff
abbrev liftCoeff := algebraMap Coeff Base

abbrev full : MvPolynomial (Fin 5) Base :=
  normalizedFullSextic (fun e : FullSexticTailIndex => liftCoeff (X e))

def coefficients : CoeffRing →+* Base :=
  eval₂Hom (liftCoeff.comp C) (fun e => full.coeff (fullExponentOf e.val))

theorem full_equation : CycleQ2GeometricHodgeThreefold.equation coefficients = full := by
  rw [CycleQ2GeometricHodgeThreefold.equation, universalF, map_fullInvariantPolynomial]
  refine (congrArg (fullInvariantPolynomial 6) ?_).trans
    (fullInvariantPolynomial_of_homogeneous (normalizedFullSextic_homogeneous _))
  funext e
  exact eval₂Hom_X' _ _ e

abbrev rawChart : MvPolynomial (Fin 4) Coeff := chart (normalizedFullSextic (fun e : FullSexticTailIndex => (X e : Coeff)))

theorem raw_chart_equation : CycleQ2HodgeEuler.F coefficients 0 =
    MvPolynomial.map liftCoeff rawChart := by
  change CycleQ2HodgeEuler.dehom 0 (CycleQ2GeometricHodgeThreefold.equation coefficients) = _
  rw [full_equation, ← CycleQ2MonicWeightedAffineEquation.chart_eq_dehom,
    rawChart, CycleQ2WeightedAffineChartJets.map_chart]
  congr 1
  simp only [full, normalizedFullSextic, map_add, map_sum, map_monomial, map_one]

end CycleQ2WeightedConeUniversal
end

#print axioms CycleQ2WeightedConeUniversal.raw_chart_equation
