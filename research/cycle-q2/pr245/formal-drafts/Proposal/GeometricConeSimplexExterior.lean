import Proposal.GeometricConeSimplexRings
import Proposal.GeometricLogarithmicFractions
import Proposal.GeometricLogarithmicChartDerivative
import Proposal.ScratchLogFractionComparison

/-! Exterior restriction from each gradient localization of the cone into
the common five-variable fraction field. The rank-five coordinate frame
is exact on both rings. In particular comparison in the fraction field
detects equality of regular numerators, and commutes with restriction to
every higher simplex. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2ConeSimplexExterior

open MvPolynomial CycleQ2ConeSimplexRings
open CycleQ2WeightedCechPresentations (denominators)
open CycleQ2LogarithmicPullback (Forms differential differential_D restrict_comp)
open CycleQ2LogarithmicChartDerivative (pull pull_d)
open CycleQ2LogPolynomialFrame (localizedBasis localizedBasis_apply)
open CycleQ2LogFractionComparison (ambientFrame)
open CycleQ2LogarithmicDifferential (exteriorD)

variable {k : Type} [Field k] [CharZero k]
variable (G : P k) (T : Finset (Fin 5))
local notation "K" => FractionRing (P k)

abbrev regularFrame := localizedBasis (Fin 5) (Ambient G T) (denominators G (T : Set (Fin 5)))
abbrev fracFrame := ambientFrame (I := Fin 5) (k := k)

variable (hT : ∀ i ∈ T, pderiv i G ≠ 0)

/-- Pullback of the regular frame to the rational ambient frame preserves each coordinate. -/
theorem embed_basis (i : Fin 5) :
    differential (embed G T hT) (regularFrame G T i) = fracFrame (k := k) i := by
  change differential (embed G T hT) (localizedBasis _ _ _ i) = localizedBasis _ _ _ i
  rw [localizedBasis_apply, differential_D, embed_polynomial, localizedBasis_apply]

/-- Rational exterior forms distinguish regular numerators on each gradient simplex. -/
theorem pull_embed_injective (n : ℕ) : Function.Injective (pull (embed G T hT) n) :=
  CycleQ2LogarithmicFractions.pull_injective (embed G T hT).toRingHom (embed_injective G T hT)
    (differential (embed G T hT)) (regularFrame G T) (fracFrame (k := k))
    (embed_basis G T hT) n

/-- The ambient exterior derivative on the fraction field extends the one on the simplex. -/
theorem pull_embed_d (n : ℕ) (ω : Forms k (Ambient G T) n) :
    exteriorD (fracFrame (k := k)) n (pull (embed G T hT) n ω) =
      pull (embed G T hT) (n+1) (exteriorD (regularFrame G T) n ω) :=
  pull_d _ (regularFrame G T) _ (localizedBasis_apply _ _ _)
    (fracFrame (k := k)) _ (localizedBasis_apply _ _ _) n ω

variable {T} {U : Finset (Fin 5)}

/-- Embedding after restriction into a larger intersection agrees identically
with the original embedding on exterior powers, including on repeated vertices. -/
theorem pull_embed_restrict (h : T ⊆ U) (hU : ∀ i ∈ U, pderiv i G ≠ 0)
    (n : ℕ) (ω : Forms k (Ambient G T) n) :
    pull (embed G U hU) n (pull (restrictAmbient G h) n ω) =
      pull (embed G T (fun i hi => hU i (h hi))) n ω := by
  calc
    _ = pull ((embed G U hU).comp (restrictAmbient G h)) n ω :=
      (restrict_comp (restrictAmbient G h) (embed G U hU) n ω).symm
    _ = _ := by rw [embed_restrict]

variable (T)

/-- Simple meromorphic pole represented by a regular chart numerator. -/
def fraction (n : ℕ) : Forms k (Ambient G T) n →+ Forms k K n :=
  ((algebraMap (P k) K G)⁻¹ : K) • (pull (embed G T hT) n).toAddMonoidHom

@[simp] theorem fraction_apply (n : ℕ) (ω : Forms k (Ambient G T) n) :
    fraction G T hT n ω =
      ((algebraMap (P k) K G)⁻¹ : K) • pull (embed G T hT) n ω := rfl

theorem fraction_injective (hG : G ≠ 0) (n : ℕ) : Function.Injective (fraction G T hT n) := by
  have hF : algebraMap (P k) K G ≠ 0 :=
    fun hf => hG (IsFractionRing.to_map_eq_zero_iff.mp hf)
  intro a b hab
  apply pull_embed_injective G T hT n
  have h := congrArg (fun v : Forms k K n => algebraMap (P k) K G • v) hab
  simpa only [fraction_apply, smul_smul, mul_inv_cancel₀ hF, one_smul] using h

variable {T}

/-- Restricting the regular numerator of a simple pole preserves the meromorphic form. -/
theorem fraction_restrict (h : T ⊆ U) (hU : ∀ i ∈ U, pderiv i G ≠ 0)
    (n : ℕ) (ω : Forms k (Ambient G T) n) :
    fraction G U hU n (pull (restrictAmbient G h) n ω) =
      fraction G T (fun i hi => hU i (h hi)) n ω := by
  rw [fraction_apply, fraction_apply, pull_embed_restrict]

end CycleQ2ConeSimplexExterior
end
#print axioms CycleQ2ConeSimplexExterior.pull_embed_injective
#print axioms CycleQ2ConeSimplexExterior.fraction_restrict
