import Proposal.GeometricConeSimplexRings
import Proposal.GeometricConeSimplexCofactor
import Proposal.GeometricLogarithmicPullback
import Proposal.ScratchLogCofactorClosure
import Proposal.ScratchWeightedCechPresentations
import Proposal.WeightedConeEuler

/-! Regular simple-pole numerators of the literal sextic on gradient intersections. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2ConeSimplexNumerator

open MvPolynomial
open CycleQ2ConeSimplexRings (Ambient embed embed_polynomial)
open CycleQ2GeometricHodgeThreefold (equation equation_homogeneous)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2WeightedConePartial (RF value)
open CycleQ2WeightedConeVertex (coneNumerator)
open CycleQ2WeightedCechPresentations (denominators weight)
open CycleQ2WeightedLocalPresentations (Represented)
open CycleQ2WeightedDoublePoleCech (vertex edge face)
open CycleQ2LogarithmicDifferential (Form coordDeriv)
open CycleQ2LogPolynomialFrame (localizedBasis localizedBasis_apply coordDeriv_polynomial)
open CycleQ2LogFractionComparison (ambientFrame)
open CycleQ2LogCofactorClosure (half vertexMer edgeMer faceMer)
open CycleQ2LogarithmicPullback (differential differential_D)
open CycleQ2GeometricExteriorSheaf (exteriorMap)

variable {k : Type} [Field k] [CharZero k] (φ : CoeffRing →+* k) (T : Finset (Fin 5))
local notation "P" => MvPolynomial (Fin 5) k
local notation "K" => RF (Fin 5) k
local notation "G" => equation φ
local notation "M" => denominators G (T : Set (Fin 5))
local notation "A" => Ambient G T
local notation "B" => ambientFrame (I := Fin 5) (k := k)
local notation "D" => coordDeriv B
local notation "F" => value G
local notation "N" => value (coneNumerator k)

abbrev regularBasis : Module.Basis (Fin 5) A (KaehlerDifferential k A) :=
  localizedBasis (Fin 5) A M

variable (hT : ∀ a ∈ T, pderiv a G ≠ 0)
local notation "σ" => embed G T hT

theorem regularBasis_field (a : Fin 5) :
    differential σ (regularBasis φ T a) = B a := by
  rw [regularBasis, localizedBasis_apply, differential_D, embed_polynomial]
  exact (localizedBasis_apply (Fin 5) K (nonZeroDivisors P) a).symm

private theorem deriv_poly (i : Fin 5) (p : P) : D i (value p) = value (pderiv i p) :=
  coordDeriv_polynomial (Fin 5) K (nonZeroDivisors P) i p

private theorem dn (i : Fin 5) (hi : i ∈ T) : value (pderiv i G) ≠ 0 :=
  fun h => hT i hi (IsFractionRing.to_map_eq_zero_iff.mp h)

private theorem fn (i : Fin 5) (hi : i ∈ T) : F ≠ 0 := by
  intro h
  have hG : G = 0 := IsFractionRing.to_map_eq_zero_iff.mp h
  exact hT i hi (by rw [hG, map_zero])

private theorem withHalf {z : K} {d : ℤ} (hz : Represented value M d z) :
    Represented value M d (half * z) := by
  have hc : Represented value M 0 (half (k := k)) := by
    change Represented value M 0 (algebraMap k K (2 : k)⁻¹)
    rw [IsScalarTower.algebraMap_apply k P K]
    exact Represented.constant value M _
  simpa only [zero_add] using hc.mul hz

private theorem lift_exists {z : K} {d : ℤ} (hz : Represented value M d z) :
    ∃ c : A, Represented (algebraMap P A) M d c ∧ σ c = half * z :=
  (withHalf φ T hz).liftToLocalization σ.toRingHom (embed_polynomial G T hT)

private def liftCoeff {z : K} {d : ℤ} (hz : Represented value M d z) : A :=
  (lift_exists φ T hT hz).choose

private theorem liftCoeff_spec {z : K} {d : ℤ} (hz : Represented value M d z) :
    Represented (algebraMap P A) M d (liftCoeff φ T hT hz) ∧
      σ (liftCoeff φ T hT hz) = half * z :=
  (lift_exists φ T hT hz).choose_spec

private theorem repV (i : Fin 5) (hi : i ∈ T) :
    Represented value M 0 (F * vertex D F N i) :=
  CycleQ2WeightedCechPresentations.vertex_numerator (equation_homogeneous φ)
    CycleQ2WeightedConeEuler.numerator_homogeneous deriv_poly (fn φ T hT i hi)
    hi (dn φ T hT i hi)

private theorem repE (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (a : Fin 5) :
    Represented value M (weight a) (F * edge D F N i j a) :=
  CycleQ2WeightedCechPresentations.edge_numerator (equation_homogeneous φ)
    CycleQ2WeightedConeEuler.numerator_homogeneous deriv_poly (fn φ T hT i hi)
    hi hj (dn φ T hT) a

private theorem repF (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) (a b : Fin 5) :
    Represented value M (weight a + weight b) (F * face D F N i j l a b) :=
  CycleQ2WeightedCechPresentations.face_numerator (equation_homogeneous φ)
    CycleQ2WeightedConeEuler.numerator_homogeneous deriv_poly (fn φ T hT i hi)
    hi hj hl (dn φ T hT) a b

/-- Polynomial fractions of degree zero, wₐ and wₐ+wᵦ, on the same
intersection as the corresponding simplex. Each coefficient includes the
factor 1/2 appearing in the comparison with the original cubic pole. -/
def vCoeff (i : Fin 5) (hi : i ∈ T) : A := liftCoeff φ T hT (repV φ T hT i hi)
def eCoeff (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (a : Fin 5) : A :=
  liftCoeff φ T hT (repE φ T hT i j hi hj a)
def fCoeff (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) (a b : Fin 5) : A :=
  liftCoeff φ T hT (repF φ T hT i j l hi hj hl a b)

theorem vCoeff_repr (i : Fin 5) (hi : i ∈ T) :
    Represented (algebraMap P A) M 0 (vCoeff φ T hT i hi) :=
  (liftCoeff_spec φ T hT (repV φ T hT i hi)).1

theorem eCoeff_repr (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (a : Fin 5) :
    Represented (algebraMap P A) M (weight a) (eCoeff φ T hT i j hi hj a) :=
  (liftCoeff_spec φ T hT (repE φ T hT i j hi hj a)).1

theorem fCoeff_repr (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) (a b : Fin 5) :
    Represented (algebraMap P A) M (weight a + weight b) (fCoeff φ T hT i j l hi hj hl a b) :=
  (liftCoeff_spec φ T hT (repF φ T hT i j l hi hj hl a b)).1

theorem vCoeff_field (i : Fin 5) (hi : i ∈ T) :
    σ (vCoeff φ T hT i hi) = half * (F * vertex D F N i) :=
  (liftCoeff_spec φ T hT (repV φ T hT i hi)).2

theorem eCoeff_field (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (a : Fin 5) :
    σ (eCoeff φ T hT i j hi hj a) = half * (F * edge D F N i j a) :=
  (liftCoeff_spec φ T hT (repE φ T hT i j hi hj a)).2

theorem fCoeff_field (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) (a b : Fin 5) :
    σ (fCoeff φ T hT i j l hi hj hl a b) = half * (F * face D F N i j l a b) :=
  (liftCoeff_spec φ T hT (repF φ T hT i j l hi hj hl a b)).2

/-- Regular simple-pole numerators on derivative opens of the affine cone. -/
def v (i : Fin 5) (hi : i ∈ T) : Form k A 5 :=
  CycleQ2ConeSimplexCofactor.top (regularBasis φ T) (vCoeff φ T hT i hi)

def e (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) : Form k A 4 :=
  CycleQ2ConeSimplexCofactor.flux (regularBasis φ T) (eCoeff φ T hT i j hi hj)

def f (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) : Form k A 3 :=
  CycleQ2ConeSimplexCofactor.biv (regularBasis φ T) (fCoeff φ T hT i j l hi hj hl)

local notation "pull" => exteriorMap σ.toRingHom (differential σ)

theorem v_field (i : Fin 5) (hi : i ∈ T) :
    pull 5 (v φ T hT i hi) = F • vertexMer φ i := by
  rw [v, CycleQ2ConeSimplexCofactor.top_map σ _ B (regularBasis_field φ T hT), vCoeff_field]
  change CycleQ2LogCofactorRealization.top B (half • (F • vertex D F N i)) =
    F • (half • CycleQ2LogCofactorRealization.top B (vertex D F N i))
  rw [map_smul, map_smul, smul_comm]

theorem e_field (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) :
    pull 4 (e φ T hT i j hi hj) = F • edgeMer φ i j := by
  rw [e, CycleQ2ConeSimplexCofactor.flux_map σ _ B (regularBasis_field φ T hT)]
  simp only [eCoeff_field]
  change CycleQ2LogCofactorRealization.flux B (half • (F • edge D F N i j)) =
    F • (half • CycleQ2LogCofactorRealization.flux B (edge D F N i j))
  rw [map_smul, map_smul, smul_comm]

theorem f_field (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) :
    pull 3 (f φ T hT i j l hi hj hl) = F • faceMer φ i j l := by
  rw [f, CycleQ2ConeSimplexCofactor.biv_map σ _ B (regularBasis_field φ T hT)]
  simp only [fCoeff_field]
  change CycleQ2LogCofactorRealization.biv B (half • (F • face D F N i j l)) =
    F • (half • CycleQ2LogCofactorRealization.biv B (face D F N i j l))
  rw [map_smul, map_smul, smul_comm]

end CycleQ2ConeSimplexNumerator
end

#print axioms CycleQ2ConeSimplexNumerator.v_field
#print axioms CycleQ2ConeSimplexNumerator.e_field
#print axioms CycleQ2ConeSimplexNumerator.f_field
