import Proposal.GeometricHodgeCoordinateVolume
import Proposal.GeometricHodgeFermatYukawaRows
import Proposal.GeometricHodgeFermatCechBoundary

/-!
# The oriented residue on the common Fermat overlap

The actual projective residue is the exterior product of the three free
coordinate differentials divided by the normalized x₁ partial.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeFermatOverlapVolume

open AlgebraicGeometry CategoryTheory Opposite
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeTwistRatios
open CycleQ2HodgeFermatNormalLifts (ψ)
open CycleQ2HodgeFermatCechBoundary (smooth_parameter)
open CycleQ2GeometricExteriorSheaf (exteriorSection)
open CycleQ2HodgeEulerTangentSheaf (cotangent)

abbrev f := toBase ψ
abbrev coordIndex := CycleQ2HodgeCoordinateVolume.coordIndex
variable (W : (threefold ψ).Opens) (h : ∀ i : Fin 4, W ≤ U ψ i)
abbrev forms := CycleQ2HodgeCoordinateVolume.forms ψ W (h 0)
abbrev restrictedOmega := CycleQ2HodgeCoordinateVolume.restrictedOmega ψ smooth_parameter W

theorem common_volume :
    restrictedOmega W = exteriorSection (threefold ψ).sheaf (cotangent f).val 3 W
      (CycleQ2HodgeFermatYukawaRows.d W h 1 • exteriorPower.ιMulti _ 3 (forms W h)) := by
  rw [map_smul, ← CycleQ2HodgeCoordinateVolume.partial_volume ψ smooth_parameter W (h 0),
    ← mul_smul, CycleQ2HodgeFermatYukawaRows.inverse_partial, one_smul]

end CycleQ2HodgeFermatOverlapVolume
end
#print axioms CycleQ2HodgeFermatOverlapVolume.common_volume
