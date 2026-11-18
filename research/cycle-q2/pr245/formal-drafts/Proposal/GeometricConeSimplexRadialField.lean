import Proposal.GeometricConeSimplexNumerator
import Proposal.GeometricConeSimplexExterior
import Proposal.GeometricPoleReductionRadial
import Proposal.ScratchLogNormalizedEulerCech

/-!
# The regular weighted numerators and their meromorphic Euler contractions

The weighted Euler field on each gradient localization and the Euler covector
on the rational function field have the same values on all five coordinate
differentials. This identifies the signed contractions of the regular
numerators with the normalized meromorphic representative, after clearing its
single factor of the sextic equation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2ConeSimplexRadialField

open MvPolynomial (X pderiv)
open CycleQ2ConeSimplexRings (Ambient embed embed_polynomial)
open CycleQ2ConeSimplexNumerator (regularBasis regularBasis_field v e f v_field e_field f_field)
open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2LogarithmicDifferential (Form)
open CycleQ2LogFractionComparison (ambientFrame)
open CycleQ2WeightedConePartial (RF value)
open CycleQ2WeightedCechPresentations (denominators)
open CycleQ2LogarithmicPullback (differential)
open CycleQ2LogarithmicChartDerivative (pull)
open CycleQ2LiteralThreefoldResidueContraction (interior interior_natural)
open CycleQ2LogCofactorClosure (vertexMer edgeMer faceMer)

variable {k : Type} [Field k] [CharZero k] (φ : CoeffRing →+* k) (T : Finset (Fin 5))
local notation "P" => MvPolynomial (Fin 5) k
local notation "K" => RF (Fin 5) k
local notation "G" => equation φ
local notation "M" => denominators G (T : Set (Fin 5))
local notation "A" => Ambient G T
local notation "B" => ambientFrame (I := Fin 5) (k := k)
local notation "E" => (CycleQ2PoleReductionRadial.radial M).liftKaehlerDifferential
local notation "L" => CycleQ2LogHomogeneousCone.radial K (nonZeroDivisors P)

private theorem field_coordinate (i : Fin 5) :
    L (B i) = (geometricWeight i : K) * value (X i) := by
  change (∑ j : Fin 5, ((geometricWeight j : K) * value (X j)) • B.coord j) (B i) = _
  simp only [LinearMap.sum_apply, LinearMap.smul_apply, Module.Basis.coord_apply,
    Module.Basis.repr_self_apply, smul_eq_mul]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hj
    simp [Ne.symm hj]
  · simp

private theorem chart_coordinate (i : Fin 5) :
    E (regularBasis φ T i) = geometricWeight i • algebraMap P A (X i) := by
  rw [regularBasis, CycleQ2LogPolynomialFrame.localizedBasis_apply,
    Derivation.liftKaehlerDifferential_comp_D, CycleQ2PoleReductionRadial.radial_map,
    CycleQ2PoleReductionRadial.polynomialEuler_X, map_nsmul]

variable (hT : ∀ i ∈ T, pderiv i G ≠ 0)
local notation "σ" => embed G T hT

theorem covector_embed (x : KaehlerDifferential k A) : L (differential σ x) = σ (E x) := by
  have hx : x ∈ Submodule.span A (Set.range (regularBasis φ T)) := by
    rw [(regularBasis φ T).span_eq]
    trivial
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨i,rfl⟩ := hy
    rw [regularBasis_field, field_coordinate, chart_coordinate, map_nsmul, embed_polynomial,
      nsmul_eq_mul]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx =>
    simp only [map_smulₛₗ, map_smul, RingHom.id_apply, hx, smul_eq_mul, map_mul] <;> rfl

/-- The actual ambient embedding intertwines contractions in every degree. -/
theorem pull_radial (n : ℕ) (m : Form k A (n+1)) :
    pull σ n (interior n E m) = interior n L (pull σ (n+1) m) :=
  (interior_natural σ.toRingHom (differential σ) E L (covector_embed φ T hT) n m).symm

def vr (i : Fin 5) (hi : i ∈ T) : Form k A 4 := interior 4 E (v φ T hT i hi)

def er (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) : Form k A 3 :=
  -interior 3 E (e φ T hT i j hi hj)

def fr (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) : Form k A 2 :=
  interior 2 E (f φ T hT i j l hi hj hl)

theorem vr_field (i : Fin 5) (hi : i ∈ T) :
    pull σ 4 (vr φ T hT i hi) = value G • CycleQ2LogNormalizedEulerCech.v φ i := by
  simp only [vr, pull_radial, v_field, vertexMer, CycleQ2LogNormalizedEulerCech.v, map_smul] <;> rfl

theorem er_field (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) :
    pull σ 3 (er φ T hT i j hi hj) = value G • CycleQ2LogNormalizedEulerCech.e φ i j := by
  simp only [er, map_neg, pull_radial, e_field, edgeMer, CycleQ2LogNormalizedEulerCech.e,
    map_smul, smul_neg] <;> rfl

theorem fr_field (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) :
    pull σ 2 (fr φ T hT i j l hi hj hl) =
      value G • CycleQ2LogNormalizedEulerCech.f φ i j l := by
  simp only [fr, pull_radial, f_field, faceMer, CycleQ2LogNormalizedEulerCech.f, map_smul] <;> rfl

section Restrictions
variable {T} {U : Finset (Fin 5)} (h : T ⊆ U) (hU : ∀ a ∈ U, pderiv a G ≠ 0)
local notation "r" => CycleQ2ConeSimplexRings.restrictAmbient G h
local notation "hT'" => (fun a ha => hU a (h ha))

theorem vr_restrict (i : Fin 5) (hi : i ∈ T) :
    pull r 4 (vr φ T hT' i hi) = vr φ U hU i (h hi) := by
  apply CycleQ2ConeSimplexExterior.pull_embed_injective G U hU 4
  rw [CycleQ2ConeSimplexExterior.pull_embed_restrict G h hU, vr_field, vr_field]

theorem er_restrict (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) :
    pull r 3 (er φ T hT' i j hi hj) = er φ U hU i j (h hi) (h hj) := by
  apply CycleQ2ConeSimplexExterior.pull_embed_injective G U hU 3
  rw [CycleQ2ConeSimplexExterior.pull_embed_restrict G h hU, er_field, er_field]

theorem fr_restrict (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) :
    pull r 2 (fr φ T hT' i j l hi hj hl) = fr φ U hU i j l (h hi) (h hj) (h hl) := by
  apply CycleQ2ConeSimplexExterior.pull_embed_injective G U hU 2
  rw [CycleQ2ConeSimplexExterior.pull_embed_restrict G h hU, fr_field, fr_field]

end Restrictions
end CycleQ2ConeSimplexRadialField
end
#print axioms CycleQ2ConeSimplexRadialField.pull_radial
#print axioms CycleQ2ConeSimplexRadialField.vr_field
#print axioms CycleQ2ConeSimplexRadialField.er_field
#print axioms CycleQ2ConeSimplexRadialField.fr_field
