import Proposal.ScratchWeightedNativeHorizontal
import Proposal.ScratchWeightedNativeCoefficient

/-! A finite homogeneous coordinate expansion determines one projected section on any native overlap. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedRepresentedForms
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2WeightedConeChartRestrictions
open CycleQ2WeightedChartShear (coordWedge exteriorWeight)
open CycleQ2WeightedNativeCoefficient (polynomials coefficient_glue)
open CycleQ2WeightedNativeHorizontal (euler native_radial_glue)
open CycleQ2WeightedLocalPresentations (Represented)
open CycleQ2HodgeEuler (overlap)
open CycleQ2HodgeEulerContractionRestriction (pull)
open CycleQ2LiteralThreefoldResidueContraction (interior)
open scoped KaehlerDifferential

variable {k S : Type} [CommRing k] [CommRing S] [Algebra k S]
variable (φ : CoeffRing →+* k) (M : Submonoid (P k))
local notation "C" => coneDivisor φ M

/-- A finite coordinate expansion on the actual localized cone divisor.
Each coefficient is represented as a homogeneous polynomial fraction of the
opposite degree to its wedge, with denominator in the patch monoid. -/
structure Expansion (m : ℕ) (ω : ⋀[C]^m Ω[C⁄k]) where
  index : Type
  terms : Finset index
  wedge : index → Fin m → Fin 5
  coefficient : index → C
  formula : ω = ∑ a ∈ terms, coefficient a • coordWedge (k := k) (coord φ M) (wedge a)
  homogeneous : ∀ a ∈ terms, Represented (polynomials φ M) M (-(exteriorWeight (wedge a) : ℤ)) (coefficient a)

abbrev projected (n : ℕ) := interior (n+1) (euler φ M).liftKaehlerDifferential

/-- Restriction of the projected expansion along the two coordinate normalizations agrees. -/
theorem projected_glue (i j : Fin 4) (g : overlap φ i j →ₐ[k] S)
    (hx : ∀ m : M, IsUnit (MvPolynomial.aeval (oldPoint φ i j g) (m : P k)))
    (hy : ∀ m : M, IsUnit (MvPolynomial.aeval (newPoint φ i j g) (m : P k)))
    (n : ℕ) (ω : ⋀[C]^(n+2) Ω[C⁄k]) (E : Expansion φ M (n+2) ω) :
    pull (newCone φ M i j g hy) (n+1) (projected φ M n ω) =
      pull (oldCone φ M i j g hx) (n+1) (projected φ M n ω) := by
  rw [E.formula]
  exact native_radial_glue φ M i j g hx hy E.terms n E.wedge E.coefficient
    (fun a ha => coefficient_glue φ M i j g hx hy (E.homogeneous a ha))

end CycleQ2WeightedRepresentedForms
end
#print axioms CycleQ2WeightedRepresentedForms.projected_glue
