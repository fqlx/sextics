import Proposal.GeometricPoleReductionLocal
import Proposal.SolutionSupport07Part01
import Proposal.SolutionSupport02Part02
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Localization.Module

/-!
# Normal contraction on the actual gradient localizations of the weighted cone

Every inverted spatial partial supplies a normalized derivation there. The
localized coordinate Kähler basis identifies these rings with the rank-five
hypothesis of the normal wedge identities for the full sextic numerator.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2PoleReductionGradient

open MvPolynomial CycleQ2GenericSexticGradient (CoeffRing universalF)
open CycleQ2LiteralThreefoldResidueContraction (interior)
open CycleQ2PoleReductionLocal

variable {K : Type} [CommRing K]
abbrev Poly (K : Type) [CommRing K] := MvPolynomial (Fin 5) K
variable (S : Submonoid (Poly K))
local notation "B" => Localization S
local notation "ΩB" => KaehlerDifferential K B
local notation "ι" => algebraMap (Poly K) B

def coordinates : Module.Basis (Fin 5) B ΩB :=
  (KaehlerDifferential.mvPolynomialBasis K (Fin 5)).ofIsLocalizedModule B S
    (KaehlerDifferential.map K K (Poly K) B)

@[simp] theorem coordinates_apply (j : Fin 5) :
    coordinates S j = KaehlerDifferential.D K B (ι (X j)) := by
  rw [coordinates, Module.Basis.ofIsLocalizedModule_apply,
    KaehlerDifferential.mvPolynomialBasis_apply, KaehlerDifferential.map_D]

def partial (i : Fin 5) : Derivation K B B :=
  CycleQ2LocalizationDerivation.extend S (pderiv i)

@[simp] theorem partial_map (i : Fin 5) (p : Poly K) :
    partial S i (ι p) = ι (pderiv i p) := CycleQ2LocalizationDerivation.extend_map S (pderiv i) p

/-- In the localized exact coordinate basis the ordinary partial has its
usual dual covector on the whole cotangent module. -/
theorem partial_covector (i : Fin 5) :
    (partial S i).liftKaehlerDifferential = (coordinates S).coord i := by
  apply (coordinates S).ext
  intro j
  rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply, coordinates_apply,
    Derivation.liftKaehlerDifferential_comp_D, partial_map]
  by_cases h : j = i
  · subst j
    simp
  · simp [pderiv_X_of_ne h, h]

/-- The normalized ith coordinate vector field on an arbitrary simultaneous
localization of the actual cone coordinates. -/
def normal (G : Poly K) (i : Fin 5) (hi : pderiv i G ∈ S) : Derivation K B B :=
  let u := (IsLocalization.map_units B (⟨pderiv i G, hi⟩ : S)).unit
  (↑u⁻¹ : B) • partial S i

@[simp] theorem normal_equation (G : Poly K) (i : Fin 5) (hi : pderiv i G ∈ S) :
    normal S G i hi (ι G) = 1 := by
  let u := (IsLocalization.map_units B (⟨pderiv i G, hi⟩ : S)).unit
  change (↑u⁻¹ : B) * partial S i (ι G) = 1
  rw [partial_map]
  exact u.inv_mul

/-- Multiplying the coefficient of a constant double contraction by f
contributes exactly this wedge in the Leibniz rule for exterior d. -/
theorem differential_double_contraction (i j : Fin 5) (f : B) (W : ⋀[B]^5 ΩB) :
    let pi := (partial S i).liftKaehlerDifferential
    let pj := (partial S j).liftKaehlerDifferential
    prepend 3 (KaehlerDifferential.D K B f) (interior 3 pi (interior 4 pj W)) =
      partial S i f • interior 4 pj W - partial S j f • interior 4 pi W := by
  dsimp only
  rw [top_double_wedge (coordinates S), Derivation.liftKaehlerDifferential_comp_D,
    Derivation.liftKaehlerDifferential_comp_D]

def weightedEquation (φ : CoeffRing →+* K) : Poly K := MvPolynomial.map φ universalF

/-- On a gradient localization of the literal weighted family, dG wedges its
normalized contraction back to the top form. -/
theorem weighted_top_normal (φ : CoeffRing →+* K) (i : Fin 5)
    (hi : pderiv i (weightedEquation φ) ∈ S) (W : ⋀[B]^5 ΩB) :
    prepend 4 (KaehlerDifferential.D K B (ι (weightedEquation φ)))
      (interior 4 (normal S (weightedEquation φ) i hi).liftKaehlerDifferential W) = W := by
  apply top_normal (coordinates S)
  rw [Derivation.liftKaehlerDifferential_comp_D, normal_equation]

/-- On the intersection of two gradient opens, the normal wedge of the double
contraction equals the alternating difference on the two original opens. -/
theorem weighted_double_normal (φ : CoeffRing →+* K) (i j : Fin 5)
    (hi : pderiv i (weightedEquation φ) ∈ S) (hj : pderiv j (weightedEquation φ) ∈ S)
    (W : ⋀[B]^5 ΩB) :
    let Si := (normal S (weightedEquation φ) i hi).liftKaehlerDifferential
    let Sj := (normal S (weightedEquation φ) j hj).liftKaehlerDifferential
    prepend 3 (KaehlerDifferential.D K B (ι (weightedEquation φ)))
      (interior 3 Si (interior 4 Sj W)) = interior 4 Sj W - interior 4 Si W := by
  apply top_double_normal (coordinates S) <;>
    rw [Derivation.liftKaehlerDifferential_comp_D, normal_equation]

end CycleQ2PoleReductionGradient
end

#print axioms CycleQ2PoleReductionGradient.weighted_top_normal
#print axioms CycleQ2PoleReductionGradient.weighted_double_normal
