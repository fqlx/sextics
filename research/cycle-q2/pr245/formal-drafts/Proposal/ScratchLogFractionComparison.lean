import Proposal.ScratchLogPolynomialFrame
import Proposal.WeightedConePartial

/-! The coordinate derivations dual to the rational ambient differential frame
are the rational extensions of the spatial polynomial partial derivatives. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogFractionComparison
open CycleQ2LogarithmicDifferential CycleQ2LogPolynomialFrame CycleQ2WeightedConePartial
variable {k I : Type} [Field k] [CharZero k] [Fintype I] [LinearOrder I]

abbrev ambientFrame : Module.Basis I (RF I k) (KaehlerDifferential k (RF I k)) :=
  localizedBasis I (RF I k) (nonZeroDivisors (Pol I k))

theorem ambient_partial (i : I) :
    coordDeriv (ambientFrame (k := k) (I := I)) i = CycleQ2WeightedConePartial.partial i := by
  apply ext_fraction
  intro p
  rw [partial_map]
  exact coordDeriv_polynomial I (RF I k) (nonZeroDivisors (Pol I k)) i p

end CycleQ2LogFractionComparison
end
#print axioms CycleQ2LogFractionComparison.ambient_partial
