import Proposal.ScratchLogLiteralEulerCech

/-!
# The simple-pole representative of the original weighted four-form

The first homotopy gives twice the starting form. Division by the constant
two yields the Čech representative for N·ι_E(W)/G³ itself.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogNormalizedEulerCech

open CycleQ2LogarithmicDifferential CycleQ2LogCofactorRealization
open CycleQ2LogCofactor (volume)
open CycleQ2LiteralThreefoldResidueContraction (interior)
open CycleQ2WeightedConePartial (RF Pol value)
open CycleQ2WeightedConeVertex (coneNumerator grad)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2WeightedDoublePoleCech (vertex edge face vertexCorrection edgeCorrection)
open CycleQ2LogFractionComparison (ambientFrame)
variable {L : Type} [Field L] [CharZero L] (φ : CoeffRing →+* L)
local notation "K" => RF (Fin 5) L
local notation "S" => nonZeroDivisors (Pol (Fin 5) L)
local notation "B" => ambientFrame (I:=Fin 5) (k:=L)
local notation "D" => coordDeriv B
local notation "E" => CycleQ2LogHomogeneousCone.radial K S
local notation "N" => value (coneNumerator L)
local notation "G" => value (equation φ)
private def half : K := algebraMap L K (2:L)⁻¹

private theorem d_half (n : ℕ) (ω : Form L K n) :
    exteriorD B n (half • ω) = half • exteriorD B n ω := by
  rw [exteriorD_smul]
  simp only [half, Derivation.map_algebraMap, zero_smul, Finset.sum_const_zero, zero_add]

/-- The original meromorphic form, with weighted Euler volume. -/
def initial : Form L K 4 := (N/G^3) • interior 4 E (volume B)

def v (i : Fin 5) : Form L K 4 := half • interior 4 E (top B (vertex D G N i))
def e (i j : Fin 5) : Form L K 3 := half • (-interior 3 E (flux B (edge D G N i j)))
def f (i j l : Fin 5) : Form L K 2 := half • interior 2 E (biv B (face D G N i j l))
def u (i : Fin 5) : Form L K 3 := half • (-interior 3 E (flux B (vertexCorrection D G N i)))
def q (i j : Fin 5) : Form L K 2 := half • interior 2 E (biv B (edgeCorrection D G N i j))

/-- All weighted component and homotopy forms vanish under further
Euler contraction, as required for descent to the projective charts. -/
theorem horizontal (i j l : Fin 5) :
    interior 3 E (initial φ) = 0 ∧
    interior 3 E (v φ i) = 0 ∧ interior 2 E (e φ i j) = 0 ∧
    interior 1 E (f φ i j l) = 0 ∧ interior 2 E (u φ i) = 0 ∧
    interior 1 E (q φ i j) = 0 := by
  simp [initial, v, e, f, u, q, CycleQ2LogInteriorAnti.interior_square]

private theorem halve_initial : half • interior 4 E (top B (2*N/G^3)) = initial φ := by
  change half • interior 4 E ((2*N/G^3) • volume B) = (N/G^3) • interior 4 E (volume B)
  rw [map_smul, smul_smul]
  congr 1
  have hh : half = (2 : K)⁻¹ := by simp [half]
  rw [hh, mul_div_assoc, ← mul_assoc, inv_mul_cancel₀ (by norm_num : (2:K) ≠ 0), one_mul]

theorem closed (i j l m : Fin 5) (hi : grad i (equation φ) ≠ 0)
    (hj : grad j (equation φ) ≠ 0) (hl : grad l (equation φ) ≠ 0) :
    exteriorD B 4 (v φ i) = 0 ∧
    exteriorD B 3 (e φ i j) = v φ j-v φ i ∧
    exteriorD B 2 (f φ i j l) = -(e φ j l-e φ i l+e φ i j) ∧
    f φ j l m-f φ i l m+f φ i j m-f φ i j l = 0 := by
  obtain ⟨h₀,h₁,h₂,h₃⟩ := CycleQ2LogLiteralEulerCech.cocycle φ i j l m hi hj hl
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [v, d_half, h₀, smul_zero]
  · simp only [e, v, d_half, h₁, smul_sub]
  · simp only [e, f, d_half, h₂, smul_neg, smul_add, smul_sub]
  · simpa only [f, smul_zero, smul_sub, smul_add] using congrArg (half (L:=L) • ·) h₃

theorem cohomologous (i j l : Fin 5) (hi : grad i (equation φ) ≠ 0)
    (hj : grad j (equation φ) ≠ 0) :
    v φ i = initial φ-exteriorD B 3 (u φ i) ∧
    e φ i j = u φ i-u φ j+exteriorD B 2 (q φ i j) ∧
    f φ i j l = -q φ j l+q φ i l-q φ i j := by
  obtain ⟨h₀,h₁,h₂⟩ := CycleQ2LogLiteralEulerCech.comparison φ i j l hi hj
  refine ⟨?_, ?_, ?_⟩
  · simpa only [v, u, d_half, smul_sub, halve_initial] using congrArg (half (L:=L) • ·) h₀
  · simpa only [e, u, q, d_half, smul_sub, smul_add] using congrArg (half (L:=L) • ·) h₁
  · simpa only [f, q, smul_sub, smul_add, smul_neg] using congrArg (half (L:=L) • ·) h₂

end CycleQ2LogNormalizedEulerCech
end

#print axioms CycleQ2LogNormalizedEulerCech.closed
#print axioms CycleQ2LogNormalizedEulerCech.cohomologous

#print axioms CycleQ2LogNormalizedEulerCech.horizontal
