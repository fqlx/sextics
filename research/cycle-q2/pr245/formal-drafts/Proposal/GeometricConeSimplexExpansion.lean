import Proposal.GeometricConeSimplexCochain
import Proposal.ScratchWeightedNormalExpansion

/-! Homogeneous-coordinate certificates for all three actual simplex residues. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2ConeSimplexCochain

open MvPolynomial CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2ConeSimplexRings (Divisor coord)
open CycleQ2LogarithmicPullback (Forms)
open CycleQ2WeightedCechPresentations (denominators derivative_mem)
open CycleQ2WeightedRepresentedForms (Expansion)
open CycleQ2WeightedNormalCofactor (gradient_residue_Expansion)
open CycleQ2WeightedCofactorExpansions (top_expansion flux_expansion biv_expansion)
open CycleQ2ConeSimplexNumerator

variable {k : Type} [Field k] [CharZero k] (φ : CoeffRing →+* k)
variable (T : Finset (Fin 5))
local notation "G" => equation φ
local notation "M" => denominators G (T : Set (Fin 5))

private def emptyExpansion (hT : ¬Regular φ T) (n : ℕ) (ω : Forms k (Divisor G T) n) :
    Expansion φ M n ω where
  index := Empty
  terms := ∅
  wedge := Empty.elim
  coefficient := Empty.elim
  formula := (empty_forms φ hT n).elim _ _
  homogeneous a := Empty.elim a

private theorem basis_coordinate (i : Fin 5) : regularBasis φ T i =
    KaehlerDifferential.D k _ (coord G T i) :=
  CycleQ2LogPolynomialFrame.localizedBasis_apply (Fin 5) _ M i

def vertexExpansion {r i : Fin 5} (hr : r ∈ T) (hi : i ∈ T) : Expansion φ M 4 (rV φ T hr hi) := by
  classical
  by_cases hT : Regular φ T
  · rw [rV_eq φ hT]
    exact gradient_residue_Expansion φ M r (derivative_mem G hr) 4 _
      (top_expansion (regularBasis φ T) (basis_coordinate φ T)
        (vCoeff φ T hT i hi) (vCoeff_repr φ T hT i hi))
  · exact emptyExpansion φ T hT _ _

def edgeExpansion {r i j : Fin 5} (hr : r ∈ T) (hi : i ∈ T) (hj : j ∈ T) :
    Expansion φ M 3 (rE φ T hr hi hj) := by
  classical
  by_cases hT : Regular φ T
  · rw [rE_eq φ hT]
    exact gradient_residue_Expansion φ M r (derivative_mem G hr) 3 _
      (flux_expansion (regularBasis φ T) (basis_coordinate φ T)
        (eCoeff φ T hT i j hi hj) (eCoeff_repr φ T hT i j hi hj))
  · exact emptyExpansion φ T hT _ _

def faceExpansion {r i j l : Fin 5} (hr : r ∈ T) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) :
    Expansion φ M 2 (rF φ T hr hi hj hl) := by
  classical
  by_cases hT : Regular φ T
  · rw [rF_eq φ hT]
    exact gradient_residue_Expansion φ M r (derivative_mem G hr) 2 _
      (biv_expansion (regularBasis φ T) (basis_coordinate φ T)
        (fCoeff φ T hT i j l hi hj hl) (fCoeff_repr φ T hT i j l hi hj hl))
  · exact emptyExpansion φ T hT _ _

end CycleQ2ConeSimplexCochain
end

#print axioms CycleQ2ConeSimplexCochain.vertexExpansion
#print axioms CycleQ2ConeSimplexCochain.edgeExpansion
#print axioms CycleQ2ConeSimplexCochain.faceExpansion
