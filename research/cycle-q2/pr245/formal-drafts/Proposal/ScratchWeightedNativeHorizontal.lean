import Proposal.ScratchWeightedRadialChartGlue
import Proposal.ScratchWeightedConeChartRestrictions
import Proposal.GeometricPoleReductionRadial

/-! The two native sections of the localized sextic cone give equal
restrictions of a radially projected degree-zero differential form. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedNativeHorizontal

open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2WeightedConeChartRestrictions
open CycleQ2WeightedChartShear
open CycleQ2WeightedHorizontalChartGlue
open CycleQ2WeightedRadialExpansion
open CycleQ2HodgeEuler (overlap invPivot localCoordinate)
open CycleQ2HodgeEulerContractionRestriction (pull)
open CycleQ2LiteralThreefoldResidueContraction (interior)
open CycleQ2PoleReductionRadial (onDivisor onDivisor_mk radial radial_equation radial_homogeneous)
open scoped KaehlerDifferential

variable {k S : Type} [CommRing k] [CommRing S] [Algebra k S]
variable (φ : CoeffRing →+* k) (M : Submonoid (P k))
local notation "C" => coneDivisor φ M
local notation "X" => coord φ M
local notation "ι" => algebraMap (P k) (Localization M)

def euler : Derivation k C C := onDivisor (ι (equation φ)) 6 (radial M) (radial_equation M φ)

theorem euler_coord (j : Fin 5) :
    (euler φ M).liftKaehlerDifferential (KaehlerDifferential.D k C (X j)) =
      (geometricWeight j : C) * X j := by
  rw [Derivation.liftKaehlerDifferential_comp_D]
  change onDivisor _ _ _ _ (Ideal.Quotient.mk _ (ι (MvPolynomial.X j))) = _
  rw [onDivisor_mk, radial_homogeneous M _ _ (MvPolynomial.isWeightedHomogeneous_X _ _ _), map_mul, map_natCast]
  rfl

variable (i k' : Fin 4) (g : overlap φ i k' →ₐ[k] S)
variable (hx : ∀ m : M, IsUnit (MvPolynomial.aeval (oldPoint φ i k' g) (m : P k)))
  (hy : ∀ m : M, IsUnit (MvPolynomial.aeval (newPoint φ i k' g) (m : P k)))
local notation "π" => oldCone φ M i k' g hx
local notation "σ" => newCone φ M i k' g hy
local notation "t" => g (invPivot φ i k')
local notation "u" => g (localCoordinate φ i k' k'.castSucc)
local notation "L" => (euler φ M).liftKaehlerDifferential

/-- A homogeneous cone form with complementary coefficient weights gives a
single radially projected form on both native projective chart sections. -/
theorem native_radial_glue {ι' : Type} (s : Finset ι') (n : ℕ)
    (I : ι' → Fin (n+2) → Fin 5) (c : ι' → C)
    (hc : ∀ a ∈ s, σ (c a)*t^(exteriorWeight (I a)) = π (c a)) :
    pull σ (n+1) (interior (n+1) L (∑ a ∈ s, c a • coordWedge (k := k) X (I a))) =
      pull π (n+1) (interior (n+1) L (∑ a ∈ s, c a • coordWedge (k := k) X (I a))) := by
  exact CycleQ2WeightedRadialChartGlue.radial_chart_change π σ L t u (native_pivots_inv φ i k' g)
    X (cone_coord_scale φ M i k' g hx hy) (euler_coord φ M) s n I c hc

end CycleQ2WeightedNativeHorizontal
end
#print axioms CycleQ2WeightedNativeHorizontal.native_radial_glue
