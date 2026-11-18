import Proposal.ScratchWeightedRepresentedNormal
import Proposal.ScratchWeightedRepresentedForms
import Proposal.ScratchWeightedCofactorExpansions
import Proposal.GeometricHodgeEuler

/-!
# Ordinary residue sends sextic-weight ambient expansions to projective degree zero

The residue of each localized Čech simplex has a finite expansion on the
actual cone divisor. The coefficients have polynomial fraction certificates
of degree opposite to their remaining wedges.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2WeightedNormalCofactor

open MvPolynomial CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2PoleReductionGradient (normal)
open CycleQ2WeightedConeChartRestrictions (P coneDivisor)
open CycleQ2WeightedRadialExpansion (insertedCoefficient)
open CycleQ2WeightedCofactorExpansions (WeightedExpansion)
open CycleQ2WeightedRepresentedForms (Expansion)
open CycleQ2LogarithmicResidue (localResidue)
open scoped KaehlerDifferential

variable {k : Type} [CommRing k] (φ : CoeffRing →+* k) (M : Submonoid (P k))
local notation "B" => Localization M
local notation "ι" => algebraMap (P k) B
abbrev quotient : B →ₐ[k] coneDivisor φ M := Ideal.Quotient.mkₐ k _

def gradient_residue_Expansion (i : Fin 5) (hi : pderiv i (equation φ) ∈ M)
    (n : ℕ) (ω : ⋀[B]^(n+1) Ω[B⁄k])
    (E : WeightedExpansion ι M (fun j => ι (X j)) 6 (n+1) ω) :
    Expansion φ M n (localResidue (quotient φ M) n (normal M (equation φ) i hi) ω) where
  index := E.index × Fin (n+1)
  terms := E.terms.product Finset.univ
  wedge := fun p => p.2.removeNth (E.wedge p.1)
  coefficient := fun p => quotient φ M (insertedCoefficient
    (normalValue i (inverseGradient M (equation φ) i hi)) (E.coefficient p.1) (E.wedge p.1) p.2)
  formula := by
    rw [E.formula]
    exact gradient_residue M (quotient φ M) (equation φ) i hi E.terms n E.wedge E.coefficient
  homogeneous := by
    intro p hp
    exact gradient_residue_represented M (quotient φ M) (equation φ)
      (CycleQ2HodgeEuler.family_homogeneous φ) i hi (E.wedge p.1) (E.coefficient p.1)
      (E.homogeneous p.1 (Finset.mem_product.mp hp).1) p.2

end CycleQ2WeightedNormalCofactor
end
#print axioms CycleQ2WeightedNormalCofactor.gradient_residue_Expansion
