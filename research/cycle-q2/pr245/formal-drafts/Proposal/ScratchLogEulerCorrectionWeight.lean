import Proposal.ScratchWeightedPoleEuler

/-!
# Euler weights of the pole-reducing correction

The two rational homotopies have the same total weights as the two lower
Čech components. This allows radial contraction of the coboundary identity.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogEulerCorrectionWeight
open CycleQ2WeightedDoublePoleCech CycleQ2WeightedPoleEuler
variable {ι k K : Type*} [Fintype ι] [DecidableEq ι] [CommRing k] [Field K] [Algebra k K]
variable (D : ι → Derivation k K K) (w : ι → ℤ)
variable {E : Derivation k K K} {F B : K} {d b : ℤ}
variable (hE : EulerCommutes D w E) (hF : HasWeight E d F) (hB : HasWeight E b B)

private theorem at_index (n : ℤ) (i a : ι) {z : K}
    (hz : HasWeight E (n+w i) z) : HasWeight E (n+w a) (oneIndex i z a) := by
  by_cases h : a=i
  · subst a
    simpa [oneIndex] using hz
  · simpa [oneIndex, Pi.single_eq_of_ne h] using (zero_weight (E:=E) (n+w a))

theorem correction_vertex (i a : ι) :
    HasWeight E (b-3*d+w a) (vertexCorrection D F B i a) := by
  have hF₂ : HasWeight E (d+d) (F^2) := by simpa only [pow_two] using mul_weight hF hF
  have h₁ : HasWeight E (b-3*d+w i) (coeff D F B i / F^2) := by
    convert div_weight (coeff_weight D w hE hF hB i) hF₂ using 1 <;> ring
  have h₂ : HasWeight E (b-3*d+w i) (twiceCoeff D F B i / F) := by
    convert div_weight (twice_weight D w hE hF hB i) hF using 1 <;> ring
  apply same_weight
  · exact neg_weight (at_index w (b-3*d) i a h₁)
  · exact at_index w (b-3*d) i a h₂

private theorem at_pair (n : ℤ) (i j a c : ι) {z : K} (hz : HasWeight E (n+w i+w j) z) :
    HasWeight E (n+w a+w c) (Pi.single i (Pi.single j z) a c) := by
  by_cases h : a=i
  · subst a
    simpa only [Pi.single_eq_same] using at_index w (n+w i) j c hz
  · simpa [Pi.single_eq_of_ne h] using (zero_weight (E:=E) (n+w a+w c))

theorem correction_edge (i j a c : ι) :
    HasWeight E (b-3*d+w a+w c) (edgeCorrection D F B i j a c) := by
  have h : HasWeight E (b-3*d+w i+w j) (pairCoeff D F B i j / F) := by
    convert div_weight (pair_weight D w hE hF hB i j) hF using 1 <;> ring
  apply same_weight
  · exact at_pair w (b-3*d) i j a c h
  · apply at_pair w (b-3*d) j i a c
    simpa only [add_right_comm (b-3*d) (w j) (w i)] using h

end CycleQ2LogEulerCorrectionWeight
end
#print axioms CycleQ2LogEulerCorrectionWeight.correction_vertex
#print axioms CycleQ2LogEulerCorrectionWeight.correction_edge
