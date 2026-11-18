import Proposal.GeometricConeSimplexNumerator
import Proposal.GeometricConeSimplexExterior

/-! Restriction of the regular Čech numerators to all larger gradient intersections. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2ConeSimplexNumerator

open MvPolynomial
open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2ConeSimplexRings (Ambient embed embed_restrict embed_injective restrictAmbient)
open CycleQ2LogarithmicChartDerivative (pull)
open CycleQ2ConeSimplexExterior (pull_embed_injective pull_embed_restrict)

variable {k : Type} [Field k] [CharZero k] (φ : CoeffRing →+* k) {T U : Finset (Fin 5)}
variable (h : T ⊆ U) (hU : ∀ a ∈ U, pderiv a (equation φ) ≠ 0)
local notation "G" => equation φ
local notation "hT" => (fun a ha => hU a (h ha))
local notation "r" => restrictAmbient G h

private theorem embed_restrict_apply (c : Ambient G T) : embed G U hU (r c) = embed G T hT c :=
  DFunLike.congr_fun (embed_restrict G h hU) c

theorem vCoeff_restrict (i : Fin 5) (hi : i ∈ T) :
    r (vCoeff φ T hT i hi) = vCoeff φ U hU i (h hi) := by
  apply embed_injective G U hU
  rw [embed_restrict_apply φ h hU, vCoeff_field, vCoeff_field]

theorem eCoeff_restrict (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (a : Fin 5) :
    r (eCoeff φ T hT i j hi hj a) = eCoeff φ U hU i j (h hi) (h hj) a := by
  apply embed_injective G U hU
  rw [embed_restrict_apply φ h hU, eCoeff_field, eCoeff_field]

theorem fCoeff_restrict (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) (a b : Fin 5) :
    r (fCoeff φ T hT i j l hi hj hl a b) = fCoeff φ U hU i j l (h hi) (h hj) (h hl) a b := by
  apply embed_injective G U hU
  rw [embed_restrict_apply φ h hU, fCoeff_field, fCoeff_field]

theorem v_restrict (i : Fin 5) (hi : i ∈ T) :
    pull r 5 (v φ T hT i hi) = v φ U hU i (h hi) := by
  apply pull_embed_injective G U hU 5
  rw [pull_embed_restrict G h hU, v_field, v_field]

theorem e_restrict (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) :
    pull r 4 (e φ T hT i j hi hj) = e φ U hU i j (h hi) (h hj) := by
  apply pull_embed_injective G U hU 4
  rw [pull_embed_restrict G h hU, e_field, e_field]

theorem f_restrict (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) :
    pull r 3 (f φ T hT i j l hi hj hl) = f φ U hU i j l (h hi) (h hj) (h hl) := by
  apply pull_embed_injective G U hU 3
  rw [pull_embed_restrict G h hU, f_field, f_field]

end CycleQ2ConeSimplexNumerator
end

#print axioms CycleQ2ConeSimplexNumerator.v_restrict
#print axioms CycleQ2ConeSimplexNumerator.e_restrict
#print axioms CycleQ2ConeSimplexNumerator.f_restrict
