import Proposal.GeometricGenericWeightedMonicCoefficients
import Proposal.GeometricGenericWeightedSource
import Proposal.GeometricMonicWeightedPrimitiveIdentity
import Proposal.GeometricWeightedAffineChartJets
import Proposal.GeometricWeightedDensityNormalization

/-!
# The normalized affine sextic in the deformed function field

On the first weight-one chart, the leading coefficient scales every normal
jet of the monic equation to the corresponding jet of the actual pencil.
The three tangent operators agree after this normalization and the cubic-pole
densities differ by the cube of the leading coefficient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2GenericWeightedMonicDensity

open MvPolynomial CycleQ2GenericSpecialization CycleQ2GenericPencilLift
  CycleQ2GenericWeightedCoordinates CycleQ2GenericWeightedPencilEquation
  CycleQ2GenericWeightedChainRule CycleQ2GenericWeightedSource
  CycleQ2GenericWeightedMonicOpen CycleQ2GenericWeightedMonicCoefficients
  CycleQ2GenericWeightedOpen CycleQ2IncidenceNormalForm
  CycleQ2MonicWeightedPrimitiveIdentity CycleQ2WeightedAffineChartJets
open CycleQ2MonicWeightedAffineEquation (chart)
open CycleQ2AffineWeightedTransfer (weightedSource)
open CycleQ2Bridge (polynomialMap)
open CycleQ2GenericPencilOpen (ParameterIndex)
open scoped BigOperators

abbrev affinePoint (i : Fin 4) : RF := weightedPoint i.succ

def value (d : Direction) : Pol (coefficientField d) →+* RF :=
  eval₂Hom (algebraMap (coefficientField d) RF) affinePoint

def monicEquation (d : Direction) (c : ParameterIndex → ℂ) : Pol (coefficientField d) :=
  chart (normalizedFullSextic (coefficients d c))

private theorem lift_point : Fin.cases 1 affinePoint = weightedPoint := by
  funext i
  exact Fin.cases rfl (fun _ => rfl) i

private theorem value_rename (d : Direction) (q : Pol (coefficientField d)) :
    eval₂Hom (algebraMap (coefficientField d) RF) weightedPoint (rename Fin.succ q) = value d q := by
  rw [← lift_point, eval_rename_succ]
  rfl

private theorem map_normalized (d : Direction) (c : ParameterIndex → ℂ) :
    MvPolynomial.map (algebraMap (coefficientField d) RF) (normalizedFullSextic (coefficients d c)) =
      normalizedFullSextic (normalizedCoefficientPoint d c) := by
  simp only [normalizedFullSextic, map_add, map_sum, map_monomial, map_one]
  rfl

private theorem normal_b {R : Type} [CommRing R] :
    normal (b : Pol R) = 2 * X 0 * X 1 ^ 2 * X 2 ^ 2 * X 3 ^ 2 := by
  norm_num [normal, b, pderiv_mul, pderiv_pow, pderiv_X, Pi.single_apply, show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide]
  ring

private theorem normal_normal_b {R : Type} [CommRing R] :
    normal (normal (b : Pol R)) = 2 * X 1 ^ 2 * X 2 ^ 2 * X 3 ^ 2 := by
  have h₂ : pderiv 0 (2 : Pol R) = 0 := (pderiv 0).map_natCast 2
  rw [normal_b]
  norm_num [normal, pderiv_mul, pderiv_pow, pderiv_X, Pi.single_apply, show (2 : Fin 4) ≠ 0 by decide, show (3 : Fin 4) ≠ 0 by decide, h₂]
  ring

variable (c : ParameterIndex → ℂ) (hc : endpointDifference c ≠ 0)
local notation "ep" => endpointDirection c hc
local notation "L" => coefficientPoint ep c fullSexticLeadingIndex
local notation "Fₘ" => monicEquation ep c

variable (hL : coefficientPoint (endpointDirection c hc) c fullSexticLeadingIndex ≠ 0)
include hL

private theorem jet_polynomial (i : Fin 4) (k : ℕ) :
    (pderiv i.succ)^[k] (endpointEquation c hc) =
      C L * MvPolynomial.map (algebraMap (coefficientField ep) RF)
        ((pderiv i.succ)^[k] (normalizedFullSextic (coefficients ep c))) := by
  induction k with
  | zero => exact (equation_eq_leading_mul_normalized ep c hL).trans
      (congrArg (fun p => C L * p) (map_normalized ep c).symm)
  | succ k ih => simp only [Function.iterate_succ_apply', ih, pderiv_C_mul, pderiv_map]

theorem jet_scale (i : Fin 4) (k : ℕ) :
    eval weightedPoint ((pderiv i.succ)^[k] (endpointEquation c hc)) =
      L * value ep ((pderiv i)^[k] Fₘ) := by
  rw [jet_polynomial c hc hL, map_mul, eval_C, eval_map]
  congr 1
  change _ = eval₂Hom _ affinePoint ((pderiv i)^[k] (chart _))
  rw [iterate_pderiv_chart, eval_chart, lift_point]
  rfl

theorem value_equation : value ep Fₘ = 0 := by
  have h := (jet_scale c hc hL 0 0).symm.trans (endpoint_equation c hc)
  exact (mul_eq_zero.mp h).resolve_left hL

theorem normal_jet_scale (k : ℕ) :
    familyNormalJet ep k = L * value ep ((pderiv 0)^[k+1] Fₘ) :=
  (endpoint_normalJet c hc k).symm.trans (jet_scale c hc hL 0 (k+1))

theorem normal_ne_zero : value ep (normal Fₘ) ≠ 0 := by
  exact right_ne_zero_of_mul ((normal_jet_scale c hc hL 0).symm.trans_ne
    (familyPartial_zero_ne_zero ep))

/-- The three actual relative derivations act on every evaluated four-variable
polynomial by implicit differentiation of the normalized sextic equation. -/
theorem tangent_apply (j : Fin 3) (q : Pol (coefficientField ep)) :
    relativeDerivation ep j (value ep q) = value ep (pderiv j.succ q) -
      value ep (pderiv j.succ Fₘ) / value ep (normal Fₘ) * value ep (normal q) := by
  have h := weighted_derivative c hc j (algebraMap (coefficientField ep) RF)
    (deriv_coefficientField ep j) (rename Fin.succ q)
  have hn := jet_scale c hc hL 0 1
  have ht := jet_scale c hc hL j.succ 1
  change eval weightedPoint (pderiv 1 (endpointEquation c hc)) = L * value ep (normal Fₘ) at hn
  change eval weightedPoint (pderiv j.succ.succ (endpointEquation c hc)) =
    L * value ep (pderiv j.succ Fₘ) at ht
  have hrename (i : Fin 4) :
      pderiv i.succ (rename Fin.succ q) = rename Fin.succ (pderiv i q) :=
    pderiv_rename (Fin.succ_injective _) i q
  have hnq : pderiv 1 (rename Fin.succ q) = rename Fin.succ (normal q) := hrename 0
  rw [value_rename, hrename j.succ, hnq, value_rename, value_rename, ht, hn] at h
  rw [h, mul_div_assoc, mul_div_mul_left _ _ hL, mul_comm (value ep (normal q))]

/-- The monic density is the cube of the leading coefficient times the
density in the original deformed field, including both numerator jets. -/
theorem density_eq :
    density (value ep) Fₘ = L ^ 3 * genericDensity ep weightedSource := by
  have hb : value ep b = polynomialMap 4 weightedSource := by
    rw [weightedSource_value]
    simp only [value, b, map_mul, map_pow, eval₂Hom_X']
    rfl
  have hb₁ : value ep (normal b) = polynomialMap 4 (pderiv 0 weightedSource) := by
    rw [weightedSource_firstJet_value, normal_b]
    simp only [value, map_mul, map_pow, map_ofNat, eval₂Hom_X']
    rfl
  have hb₂ : value ep (normal (normal b)) = polynomialMap 4 (pderiv 0 (pderiv 0 weightedSource)) := by
    rw [weightedSource_secondJet_value, normal_normal_b]
    simp only [value, map_mul, map_pow, map_ofNat, eval₂Hom_X']
    rfl
  have hscaled : genericDensity ep weightedSource = (L ^ 3)⁻¹ * density (value ep) Fₘ := by
    unfold genericDensity density
    rw [← hb, ← hb₁, ← hb₂, normal_jet_scale c hc hL 0, normal_jet_scale c hc hL 1,
      normal_jet_scale c hc hL 2]
    exact CycleQ2WeightedDensityNormalization.normalDensity_scale _ _ _ _ _ _ _
      (normal_ne_zero c hc hL) hL
  rw [hscaled, ← mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ hL), one_mul]

theorem primitive_of_monic
    (h : ∃ v : Fin 3 → RF, (∑ j, relativeDerivation ep j (v j)) = density (value ep) Fₘ) :
    ∃ v : Fin 3 → RF, (∑ j, relativeDerivation ep j (v j)) = genericDensity ep weightedSource := by
  obtain ⟨v,hv⟩ := h
  have hconst (j : Fin 3) : relativeDerivation ep j ((L ^ 3)⁻¹) = 0 := by
    rw [Derivation.leibniz_inv, Derivation.leibniz_pow, deriv_leading]
    simp
  refine ⟨fun j => (L ^ 3)⁻¹ * v j, ?_⟩
  rw [CycleQ2WeightedDensityNormalization.divergence_mul_constant _ _ _ hconst, hv,
    density_eq c hc hL, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hL), one_mul]

end CycleQ2GenericWeightedMonicDensity
end

#print axioms CycleQ2GenericWeightedMonicDensity.tangent_apply
#print axioms CycleQ2GenericWeightedMonicDensity.density_eq
#print axioms CycleQ2GenericWeightedMonicDensity.primitive_of_monic
