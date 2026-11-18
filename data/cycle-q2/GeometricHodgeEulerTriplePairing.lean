import Proposal.GeometricHodgeEulerTripleLaws
import Proposal.GeometricHodgeEulerVolume
import Proposal.GeometricHodgeTriplePairing
import Proposal.GeometricSheafCohomologyScalar

/-!
# The native moving-family triple pairing on Čech cochains

Restrict the global Poincaré residue to the open, then apply the three
genuine tangent sections in order. The additive and restriction laws of
successive contraction supply the fields of the Čech pairing.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerTriplePairing

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open CycleQ2HodgeTripleTangentCech CycleQ2HodgeEulerContractionSheaf
open CycleQ2HodgeEulerTripleContraction CycleQ2HodgeEulerTripleLaws
open CycleQ2GeometricSheafCohomologyScalar (additiveSheaf)
open CycleQ2GeometricProjectiveHOne (structureAdditiveSheaf)
open CycleQ2GeometricDifferentialSheaf
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEulerVolume
open CycleQ2HodgeEulerTangentSheaf (tangent cotangent)
open CycleQ2GenericSexticGradient (CoeffRing)

variable {X : Scheme.{0}} (M : SheafOfModules.{0} (ringSheaf X.sheaf))

def ofGlobal (ω : Γ(form M 3,⊤)) : Pairing (X := (X : TopCat)) (additiveSheaf X.sheaf (dual M)) (structureAdditiveSheaf X) where
  eval V := evaluation M V ((form M 3).val.map (homOfLE (le_top : V ≤ ⊤)).op ω)
  natural {W V} h a b c := by
    change X.presheaf.map (homOfLE h).op (triple M V a b c _) =
      triple M W ((dual M).val.map (homOfLE h).op a) ((dual M).val.map (homOfLE h).op b)
        ((dual M).val.map (homOfLE h).op c) _
    rw [triple_restrict]
    exact congrArg (triple M W _ _ _) ((form M 3).val.map_comp_apply
      (homOfLE (le_top : V ≤ ⊤)).op (homOfLE h).op ω).symm

variable (φ : CoeffRing →+* ℂ) (hg : IsUnit (φ goodParameter))

def pairing : Pairing (X := (threefold φ : TopCat)) (additiveSheaf (threefold φ).sheaf (tangent (toBase φ)))
    (structureAdditiveSheaf (threefold φ)) :=
  ofGlobal (cotangent (toBase φ)) (omega φ hg)

theorem pairing_eval (V : (threefold φ).Opens) (a b c : Γ(tangent (toBase φ),V)) :
    (pairing φ hg).eval V a b c = triple (cotangent (toBase φ)) V a b c
      ((threeForms φ).val.map (homOfLE (le_top : V ≤ ⊤)).op (omega φ hg)) := rfl

end CycleQ2HodgeEulerTriplePairing
end

#print axioms CycleQ2HodgeEulerTriplePairing.pairing_eval
