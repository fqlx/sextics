import Proposal.GeometricConeSimplexCochain
import Proposal.ScratchWeightedRepresentedForms

/-!
# The sign and wedge on the original z₀=1, ∂₁G≠0 chart

Normal insertion in the second coordinate of the cone volume gives a minus
sign. Residue of an Euler-contracted meromorphic form gives another minus
sign. The pullback of d z₀ to z₀=1 vanishes, so only the coefficient of
d z₂∧d z₃∧d z₄ survives.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogChosenCofactor

open CycleQ2LogarithmicPullback (Forms exactWedge differential differential_D pull_exactWedge)
open CycleQ2LogarithmicResidue (localResidue residue restrict_prepend prepend_zero)
open CycleQ2PoleReductionLocal (prepend prepend_generator contract_prepend)
open CycleQ2LiteralThreefoldResidueContraction (interior interior_wedge)
open CycleQ2GeometricExteriorSheaf (exteriorMap)
open CycleQ2HodgeEulerContractionRestriction (pull pullOne pullOne_D)
open CycleQ2WeightedRepresentedForms (projected)
open CycleQ2WeightedNativeHorizontal (euler euler_coord)
open CycleQ2WeightedCechPresentations (denominators)
open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2GenericSexticGradient (CoeffRing)
open MvPolynomial

section Algebra
variable {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

def spatial (x : Fin 5 → R) : Forms k R 3 := exactWedge (k:=k) 3 (fun j : Fin 3 => x j.succ.succ)
def omitted (x : Fin 5 → R) : Forms k R 4 := prepend 3 (KaehlerDifferential.D k R (x 0)) (spatial x)

private theorem omitted_eq (x : Fin 5 → R) :
    exteriorPower.ιMulti R 4 ((1 : Fin 5).removeNth (fun i => KaehlerDifferential.D k R (x i))) =
      omitted x := by
  rw [omitted, spatial, exactWedge, prepend_generator]
  apply congrArg (exteriorPower.ιMulti R 4)
  funext j
  fin_cases j <;> rfl

/-- Normal insertion in the second coordinate of the ordered volume. -/
theorem normal_one (x : Fin 5 → R) (l : KaehlerDifferential k R →ₗ[R] R) (c : R)
    (hx : ∀ j : Fin 5, l (KaehlerDifferential.D k R (x j)) = if j=1 then c else 0) :
    interior 4 l (exactWedge (k:=k) 5 x) = -(c • omitted x) := by
  rw [exactWedge, interior_wedge, Finset.sum_eq_single (1:Fin 5)]
  · rw [hx, if_pos rfl, omitted_eq]
    change (-1 : ℤ) • _ = -_
    rw [neg_smul, one_smul]
  · intro j _ hj
    rw [hx, if_neg hj, zero_smul, smul_zero]
  · simp

theorem pull_spatial (π : R →ₐ[k] S) (x : Fin 5 → R) :
    pull π 3 (spatial x) = spatial (π ∘ x) := by
  exact pull_exactWedge π 3 _

private theorem pull_omitted (π : R →ₐ[k] S) (x : Fin 5 → R) :
    pull π 4 (omitted x) = omitted (π ∘ x) := by
  change exteriorMap π.toRingHom (pullOne π) 4 (prepend 3 _ _) = _
  rw [restrict_prepend, pullOne_D]
  exact congrArg (prepend 3 _) (pull_spatial π x)

/-- On the pivot-one section, all differential terms containing d z₀ disappear. -/
theorem pivot_slice (π : R →ₐ[k] S) (x : Fin 5 → R) (hx : π (x 0) = 1)
    (l : KaehlerDifferential k R →ₗ[R] R)
    (hl : l (KaehlerDifferential.D k R (x 0)) = x 0) :
    pull π 3 (interior 3 l (omitted x)) = spatial (π ∘ x) := by
  rw [omitted, contract_prepend, map_sub, map_smulₛₗ, hl]
  have hp : pull π 3 (prepend 2 (KaehlerDifferential.D k R (x 0)) (interior 2 l (spatial x))) = 0 := by
    change exteriorMap π.toRingHom (pullOne π) 3 _ = _
    rw [restrict_prepend, pullOne_D, hx, Derivation.map_one_eq_zero, prepend_zero]
  rw [hp, sub_zero, hx, one_smul, pull_spatial]

end Algebra

section Cone
variable {k : Type} [Field k] [CharZero k]
variable (G : MvPolynomial (Fin 5) k) (T : Finset (Fin 5)) (h : (1:Fin 5) ∈ T)
local notation "A" => CycleQ2ConeSimplexRings.Ambient G T
local notation "x" => CycleQ2ConeSimplexRings.coord G T
local notation "n₁" => CycleQ2ConeSimplexRings.normal G h

def normalValue : A := n₁ (x 1)

theorem normal_coords (j : Fin 5) :
    n₁.liftKaehlerDifferential (KaehlerDifferential.D k A (x j)) =
      if j=1 then normalValue G T h else 0 := by
  rw [Derivation.liftKaehlerDifferential_comp_D]
  by_cases e : j=1
  · subst j
    rw [if_pos rfl] <;> rfl
  · rw [if_neg e]
    change CycleQ2PoleReductionGradient.normal _ G 1 _ (algebraMap _ _ (X j)) = 0
    simp only [CycleQ2PoleReductionGradient.normal, Derivation.smul_apply,
      CycleQ2PoleReductionGradient.partial_map, pderiv_X_of_ne e, map_zero, smul_zero]

variable (φ : CoeffRing →+* k)
local notation "M" => denominators (equation φ) (T : Set (Fin 5))
local notation "π₀" => CycleQ2ConeSimplexRings.quotient (equation φ) T
local notation "ca" => CycleQ2ConeSimplexRings.coord (equation φ) T
local notation "cc" => CycleQ2WeightedConeChartRestrictions.coord φ M
local notation "C" => CycleQ2ConeSimplexRings.Divisor (equation φ) T

/-- The actual cone logarithmic residue on the chosen normal, before projective descent. -/
theorem cone_vertex (hT : CycleQ2ConeSimplexCochain.Regular φ T) :
    CycleQ2ConeSimplexCochain.rV φ T h h =
      -(π₀ (CycleQ2ConeSimplexNumerator.vCoeff φ T hT 1 h *
        normalValue (equation φ) T h) • omitted (k:=k) cc) := by
  rw [CycleQ2ConeSimplexCochain.rV_eq φ hT]
  have hw : CycleQ2ConeSimplexCofactor.volume (CycleQ2ConeSimplexNumerator.regularBasis φ T) =
      exactWedge (k:=k) 5 ca := by
    unfold CycleQ2ConeSimplexCofactor.volume exactWedge
    apply congrArg (exteriorPower.ιMulti _ 5)
    exact funext (CycleQ2LogPolynomialFrame.localizedBasis_apply _ _ _)
  change pull π₀ 4 (interior 4 (CycleQ2ConeSimplexRings.normal (equation φ) h).liftKaehlerDifferential
    (CycleQ2ConeSimplexNumerator.vCoeff φ T hT 1 h •
      CycleQ2ConeSimplexCofactor.volume (CycleQ2ConeSimplexNumerator.regularBasis φ T))) = _
  rw [hw, map_smul, normal_one ca _ _ (normal_coords (equation φ) T h), smul_neg, smul_smul,
    map_neg, map_smulₛₗ, pull_omitted] <;> rfl

/-- The second sign, from projecting the cone residue by minus Euler insertion,
gives positive spatial orientation. -/
theorem projected_vertex {S : Type} [CommRing S] [Algebra k S] (f : C →ₐ[k] S)
    (hT : CycleQ2ConeSimplexCochain.Regular φ T) (hp : f (cc 0) = 1) :
    -(pull f 3 (projected φ M 2 (CycleQ2ConeSimplexCochain.rV φ T h h))) =
      f (π₀ (CycleQ2ConeSimplexNumerator.vCoeff φ T hT 1 h *
        normalValue (equation φ) T h)) • spatial (k:=k) (f ∘ cc) := by
  rw [cone_vertex T h φ hT]
  change -(pull f 3 (interior 3 (euler φ M).liftKaehlerDifferential _)) = _
  rw [map_neg, map_smul, map_neg, map_smulₛₗ, neg_neg]
  rw [pivot_slice f cc hp (euler φ M).liftKaehlerDifferential
    (by simpa only [show CycleQ2GeometricIncidenceProj.geometricWeight 0 = 1 from rfl,
      Nat.cast_one, one_mul] using euler_coord φ M 0)]

end Cone
end CycleQ2LogChosenCofactor
end
#print axioms CycleQ2LogChosenCofactor.cone_vertex
#print axioms CycleQ2LogChosenCofactor.projected_vertex
