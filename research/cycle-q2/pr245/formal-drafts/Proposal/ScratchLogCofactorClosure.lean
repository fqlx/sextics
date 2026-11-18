import Proposal.ScratchLogCofactorRealization
import Proposal.ScratchLogFractionComparison
import Proposal.WeightedConeVertex

/-! The normalized simple poles of the weighted sextic in the ambient cone field. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogCofactorClosure

open CycleQ2LogarithmicDifferential (Form exteriorD coordDeriv exteriorD_smul)
open CycleQ2LogCofactorRealization (top flux biv)
open CycleQ2WeightedConePartial (Pol RF value)
open CycleQ2WeightedConeVertex (coneNumerator grad)
open CycleQ2WeightedDoublePoleCech (normal vertex edge face)
open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2LogFractionComparison (ambientFrame ambient_partial)
open CycleQ2LogPolynomialFrame (localizedBasis_apply)

variable {k : Type} [Field k] [CharZero k] (φ : CoeffRing →+* k)
local notation "K" => RF (Fin 5) k
local notation "B" => ambientFrame (I := Fin 5) (k := k)
local notation "D" => coordDeriv B
local notation "F" => value (equation φ)
local notation "N" => value (coneNumerator k)

abbrev half : K := algebraMap k K (2 : k)⁻¹

def vertexMer (i : Fin 5) : Form k K 5 := half • top B (vertex D F N i)

def edgeMer (i j : Fin 5) : Form k K 4 := half • flux B (edge D F N i j)

def faceMer (i j l : Fin 5) : Form k K 3 := half • biv B (face D F N i j l)

theorem normal_ne (i : Fin 5) (hi : grad i (equation φ) ≠ 0) : normal D F i ≠ 0 := by
  change coordDeriv B i (value (equation φ)) ≠ 0
  rw [ambient_partial, CycleQ2WeightedConePartial.partial_map]
  exact fun h => hi (IsFractionRing.to_map_eq_zero_iff.mp h)

theorem equation_ne (i : Fin 5) (hi : grad i (equation φ) ≠ 0) : F ≠ 0 := by
  intro h
  exact normal_ne φ i hi (by simp only [normal,h,map_zero])

theorem d_half (n : ℕ) (ω : Form k K n) :
    exteriorD B n (half • ω) = half • exteriorD B n ω := by
  rw [exteriorD_smul]
  simp only [half, Derivation.map_algebraMap, zero_smul, Finset.sum_const_zero, zero_add]

/-- The noncontracted five-, four- and three-forms of the original pole
satisfy all four Čech–de Rham equations in the common rational function field. -/
theorem ambient_closed (i j l m : Fin 5) (hi : grad i (equation φ) ≠ 0)
    (hj : grad j (equation φ) ≠ 0) (hl : grad l (equation φ) ≠ 0) :
    exteriorD B 5 (vertexMer φ i) = 0 ∧
    exteriorD B 4 (edgeMer φ i j) = vertexMer φ j - vertexMer φ i ∧
    exteriorD B 3 (faceMer φ i j l) = -(edgeMer φ j l-edgeMer φ i l+edgeMer φ i j) ∧
    faceMer φ j l m-faceMer φ i l m+faceMer φ i j m-faceMer φ i j l = 0 := by
  obtain ⟨he,hf,ht⟩ := CycleQ2LogCofactorRealization.meromorphic_form_cocycle B _
    (localizedBasis_apply (Fin 5) K (nonZeroDivisors (Pol (Fin 5) k)))
    F N i j l m (equation_ne φ i hi) (normal_ne φ i hi) (normal_ne φ j hj) (normal_ne φ l hl)
  refine ⟨?_, ?_, ?_, ?_⟩
  · letI := CycleQ2PoleReductionLocal.six_subsingleton B
    exact Subsingleton.elim _ _
  · simp only [edgeMer, vertexMer, d_half, he, smul_sub]
  · simp only [faceMer, edgeMer, d_half, hf, smul_neg, smul_add, smul_sub]
  · simpa only [faceMer, smul_sub, smul_add, smul_zero] using congrArg (half (k:=k) • ·) ht

end CycleQ2LogCofactorClosure
end

#print axioms CycleQ2LogCofactorClosure.ambient_closed
