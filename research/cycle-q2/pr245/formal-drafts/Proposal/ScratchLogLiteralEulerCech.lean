import Proposal.ScratchLogEulerRealization
import Proposal.ScratchLogEulerCorrectionWeight
import Proposal.ScratchLogFractionComparison
import Proposal.WeightedConeEuler

/-!
# Euler-contracted meromorphic representative of the actual invariant sextic

The ambient field, numerator, sextic, radial vector, and derivative opens
are the ones used in the protected computation. The uncontracted cone
five-form gives the weighted four-form by radial contraction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogLiteralEulerCech

open CycleQ2LogarithmicDifferential CycleQ2LogFractionComparison
open CycleQ2WeightedConePartial (Pol RF value partial_map)
open CycleQ2WeightedConeVertex (coneNumerator grad)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2WeightedDoublePoleCech (normal vertex edge face vertexCorrection edgeCorrection)
open CycleQ2WeightedPoleEuler (HasWeight)
open CycleQ2WeightedConeEuler (E D weight x)
open CycleQ2LogHomogeneousCone (w scalarEuler)
open CycleQ2LogEulerRealization (Cocycle Comparison)

variable {L : Type} [Field L] [CharZero L]
local notation "K" => RF (Fin 5) L
local notation "S" => nonZeroDivisors (Pol (Fin 5) L)
local notation "B" => ambientFrame (I:=Fin 5) (k:=L)
local notation "N" => value (coneNumerator L)
local notation "Λ" => scalarEuler K S
variable (φ : CoeffRing →+* L)
local notation "F" => value (equation φ)

private theorem derivs : coordDeriv B = D := funext ambient_partial

theorem scalar_radial (z : K) : Λ z = E z := by
  rw [CycleQ2WeightedConeEuler.E, CycleQ2WeightedPoleEuler.radial_apply]
  change (∑ i, (w K i * x i)* coordDeriv B i z) = _
  rw [derivs]
  simp only [w, weight, Int.cast_natCast]

private theorem degree_zero {z : K} (h : HasWeight E (-6) z) : Λ z = (-6 : K)*z := by
  rw [scalar_radial, h] <;> norm_num

private theorem degree_one (i : Fin 5) {z : K} (h : HasWeight E (-6+weight i) z) :
    Λ z = (w K i-6)*z := by
  rw [scalar_radial, h]
  push_cast
  simp only [w,weight,Int.cast_natCast]
  ring

private theorem degree_two (i j : Fin 5) {z : K} (h : HasWeight E (-6+weight i+weight j) z) :
    Λ z = (w K i+w K j-6)*z := by
  rw [scalar_radial, h]
  push_cast
  simp only [w,weight,Int.cast_natCast]
  ring

private theorem normal_ne (i : Fin 5) (hi : grad i (equation φ) ≠ 0) : normal (coordDeriv B) F i ≠ 0 := by
  rw [derivs]
  change D i (value (equation φ)) ≠ 0
  rw [CycleQ2WeightedConeEuler.D, partial_map]
  exact fun h => hi (IsFractionRing.to_map_eq_zero_iff.mp h)

private theorem equation_ne (i : Fin 5) (hi : grad i (equation φ) ≠ 0) : F ≠ 0 := by
  intro h
  exact normal_ne φ i hi (by simp only [normal,h,map_zero])

/-- On every triple of nonempty derivative opens, the meromorphic Čech
forms on the cone give the four signed closure equations after contraction
by its geometric Euler field. -/
theorem cocycle (i j l m : Fin 5) (hi : grad i (equation φ) ≠ 0)
    (hj : grad j (equation φ) ≠ 0) (hl : grad l (equation φ) ≠ 0) :
    Cocycle K S F N i j l m := by
  apply CycleQ2LogEulerRealization.cocycle_of_weights K S F N i j l m (equation_ne φ i hi)
    (normal_ne φ i hi) (normal_ne φ j hj) (normal_ne φ l hl)
  · rw [derivs]
    exact degree_zero (CycleQ2WeightedConeEuler.simplex_weights φ i j l i i).1
  · intro a
    rw [derivs]
    exact degree_one a (CycleQ2WeightedConeEuler.simplex_weights φ i j l a a).2.1
  · intro a c
    rw [derivs]
    exact degree_two a c (CycleQ2WeightedConeEuler.simplex_weights φ i j l a c).2.2

/-- The signed Euler-contracted comparison identifies the simple-pole
representative with twice the literal cubic-pole form on every pair. -/
theorem comparison (i j l : Fin 5) (hi : grad i (equation φ) ≠ 0)
    (hj : grad j (equation φ) ≠ 0) : Comparison K S F N i j l := by
  apply CycleQ2LogEulerRealization.comparison_of_weights K S F N i j l (equation_ne φ i hi)
    (normal_ne φ i hi) (normal_ne φ j hj)
  · intro a
    rw [derivs]
    apply degree_one
    exact CycleQ2LogEulerCorrectionWeight.correction_vertex D weight
      CycleQ2WeightedConeEuler.euler_commutes (CycleQ2WeightedConeEuler.equation_weight φ)
      CycleQ2WeightedConeEuler.numerator_weight i a
  · intro a c
    rw [derivs]
    apply degree_two
    exact CycleQ2LogEulerCorrectionWeight.correction_edge D weight
      CycleQ2WeightedConeEuler.euler_commutes (CycleQ2WeightedConeEuler.equation_weight φ)
      CycleQ2WeightedConeEuler.numerator_weight i j a c

end CycleQ2LogLiteralEulerCech
end
#print axioms CycleQ2LogLiteralEulerCech.cocycle
#print axioms CycleQ2LogLiteralEulerCech.comparison
