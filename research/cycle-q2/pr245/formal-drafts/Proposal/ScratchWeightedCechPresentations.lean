import Proposal.ScratchWeightedLocalPresentations
import Proposal.ScratchWeightedDoublePoleCech
import Proposal.GeometricGradientDenominators

/-!
# Homogeneous fractions for the Čech coefficients on derivative opens

Clearing the one remaining factor of the sextic leaves a vertex numerator of
weight zero, an edge numerator of weight wₐ, and a face numerator of weight
wₐ+wᵦ. Each rational function is represented by a homogeneous fraction whose
denominator is a product of the derivatives inverted on the same patch.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedCechPresentations
open MvPolynomial CycleQ2GeometricIncidenceProj CycleQ2WeightedLocalPresentations
  CycleQ2WeightedDoublePoleCech

variable {k K : Type} [CommRing k] [Field K] [Algebra k K]
local notation "P" => MvPolynomial (Fin 5) k
abbrev weight (j : Fin 5) : ℤ := geometricWeight j

variable {v : P →+* K} {D : Fin 5 → Derivation k K K} {G B : P} {T : Set (Fin 5)}
local notation "Rep" => Represented v (denominators G T)
local notation "F" => v G
local notation "N" => v B

/-- Dividing a log numerator by the gradient in the chosen normal direction
gives the coefficient of its local residue before Euler contraction. -/
theorem residue_entry (hG : G.IsWeightedHomogeneous geometricWeight 6)
    (hD : ∀ i p, D i (v p) = v (pderiv i p))
    {i : Fin 5} (hi : i ∈ T) (hne : v (pderiv i G) ≠ 0)
    {a : K} {d : ℤ} (ha : Rep d a) :
    Rep (d - 6 + weight i) (a / D i F) := by
  rw [hD i G]
  have hw := CycleQ2IncidenceChartMinor.geometricWeight_le_two i
  have hgrad : (pderiv i G).IsWeightedHomogeneous geometricWeight (6 - geometricWeight i) := by
    intro e he
    have h := derivative_degree (integer_degree hG) i he
    rw [weightZ_eq] at h
    unfold weightZ at h
    omega
  have h := ha.dividePolynomial (pderiv i G) (6 - geometricWeight i)
    hgrad (derivative_mem G hi) hne
  convert h using 1 <;> simp only [weight] <;> omega

private theorem first_value (hG : G.IsWeightedHomogeneous geometricWeight 6)
    (hN : B.IsWeightedHomogeneous geometricWeight 12) (hD : ∀ i p, D i (v p) = v (pderiv i p))
    {i : Fin 5} (hi : i ∈ T) (hne : v (pderiv i G) ≠ 0) :
    Rep (6 + weight i) (CycleQ2WeightedDoublePoleCech.coeff D F N i) := by
  have h := Represented.polynomial v (denominators G T) B 12 hN
  exact residue_entry hG hD hi hne h

private theorem second_value (hG : G.IsWeightedHomogeneous geometricWeight 6)
    (hN : B.IsWeightedHomogeneous geometricWeight 12) (hD : ∀ i p, D i (v p) = v (pderiv i p))
    {i : Fin 5} (hi : i ∈ T) (hne : v (pderiv i G) ≠ 0) :
    Rep (weight i) (twiceCoeff D F N i) := by
  have h₁ := first_value hG hN hD hi hne
  have h₂ : Rep 6 (lie D F N i) := by
    convert h₁.partial (D i) i (hD i) using 1 <;> simp only [weight] <;> ring
  convert residue_entry hG hD hi hne h₂ using 1 <;> ring

private theorem pair_value (hG : G.IsWeightedHomogeneous geometricWeight 6)
    (hN : B.IsWeightedHomogeneous geometricWeight 12) (hD : ∀ i p, D i (v p) = v (pderiv i p))
    {i j : Fin 5} (hi : i ∈ T) (hj : j ∈ T)
    (hne : ∀ u ∈ T, v (pderiv u G) ≠ 0) :
    Rep (weight i + weight j) (pairCoeff D F N i j) := by
  have h := residue_entry hG hD hj (hne j hj) (first_value hG hN hD hi (hne i hi))
  unfold pairCoeff
  rw [← div_div]
  convert h using 1 <;> ring

private theorem single_value {a : K} (j b : Fin 5) (ha : Rep (weight j) a) :
    Rep (weight b) (oneIndex j a b) := by
  by_cases h : b = j
  · subst b; simpa only [oneIndex,Pi.single_eq_same] using ha
  · simpa only [oneIndex,Pi.single_eq_of_ne h] using
      (Represented.zero v (denominators G T) (weight b))

private theorem double_value {x : K} (i j a b : Fin 5) (hx : Rep (weight i + weight j) x) :
    Rep (weight a + weight b) (twoIndex i j x a b) := by
  change Rep _ (Pi.single (M := fun _ : Fin 5 => Fin 5 → K) i
    (Pi.single (M := fun _ : Fin 5 => K) j x) a b -
    Pi.single (M := fun _ : Fin 5 => Fin 5 → K) j (Pi.single (M := fun _ : Fin 5 => K) i x) a b)
  apply Represented.sub
  · by_cases h : a = i
    · subst a
      by_cases h' : b = j
      · subst b; simpa using hx
      · simpa [Pi.single_eq_of_ne h'] using (Represented.zero v (denominators G T) (weight i + weight b))
    · simpa [Pi.single_eq_of_ne h] using (Represented.zero v (denominators G T) (weight a + weight b))
  · by_cases h : a = j
    · subst a
      by_cases h' : b = i
      · subst b; simpa [add_comm] using hx
      · simpa [Pi.single_eq_of_ne h'] using (Represented.zero v (denominators G T) (weight j + weight b))
    · simpa [Pi.single_eq_of_ne h] using (Represented.zero v (denominators G T) (weight a + weight b))

private theorem scalar_single (c x : K) (j a : Fin 5) :
    c * oneIndex j x a = oneIndex j (c*x) a := by
  by_cases h : a=j
  · subst a; simp [oneIndex]
  · simp [oneIndex,Pi.single_eq_of_ne h]

private theorem scalar_double (c x : K) (i j a b : Fin 5) :
    c * twoIndex i j x a b = twoIndex i j (c*x) a b := by
  by_cases ha : a=i <;> by_cases hj : a=j <;> by_cases hb : b=j <;> by_cases hi : b=i <;>
    simp [twoIndex,Pi.single_apply,ha,hj,hb,hi,mul_sub]

theorem vertex_numerator (hG : G.IsWeightedHomogeneous geometricWeight 6)
    (hN : B.IsWeightedHomogeneous geometricWeight 12) (hD : ∀ i p, D i (v p) = v (pderiv i p))
    (hf : F ≠ 0) {i : Fin 5} (hi : i ∈ T) (hne : v (pderiv i G) ≠ 0) :
    Rep 0 (F * vertex D F N i) := by
  rw [vertex,mul_div_cancel₀ _ hf]
  have h := second_value hG hN hD hi hne
  simpa [weight] using h.partial (D i) i (hD i)

theorem edge_numerator (hG : G.IsWeightedHomogeneous geometricWeight 6)
    (hN : B.IsWeightedHomogeneous geometricWeight 12) (hD : ∀ i p, D i (v p) = v (pderiv i p))
    (hf : F ≠ 0) {i j : Fin 5} (hi : i ∈ T) (hj : j ∈ T)
    (hne : ∀ u ∈ T, v (pderiv u G) ≠ 0) (a : Fin 5) :
    Rep (weight a) (F * edge D F N i j a) := by
  simp only [edge,Pi.sub_apply,mul_sub,scalar_single,mul_div_cancel₀ _ hf]
  have hp := pair_value hG hN hD hi hj hne
  have hpi : Rep (weight j) (D i (pairCoeff D F N i j)) := by
    convert hp.partial (D i) i (hD i) using 1 <;> simp only [weight] <;> ring
  have hpj : Rep (weight i) (D j (pairCoeff D F N i j)) := by
    convert hp.partial (D j) j (hD j) using 1 <;> simp only [weight] <;> ring
  exact (single_value j a ((second_value hG hN hD hj (hne j hj)).add hpi)).sub
    (single_value i a ((second_value hG hN hD hi (hne i hi)).add hpj))

theorem face_numerator (hG : G.IsWeightedHomogeneous geometricWeight 6)
    (hN : B.IsWeightedHomogeneous geometricWeight 12) (hD : ∀ i p, D i (v p) = v (pderiv i p))
    (hf : F ≠ 0) {i j l : Fin 5} (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T)
    (hne : ∀ u ∈ T, v (pderiv u G) ≠ 0) (a b : Fin 5) :
    Rep (weight a + weight b) (F * face D F N i j l a b) := by
  simp only [face,edgeCorrection,Pi.sub_apply,Pi.add_apply,Pi.neg_apply,mul_sub,mul_add,mul_neg,
    scalar_double,mul_div_cancel₀ _ hf]
  exact (((double_value j l a b (pair_value hG hN hD hj hl hne)).neg).add
    (double_value i l a b (pair_value hG hN hD hi hl hne))).sub
    (double_value i j a b (pair_value hG hN hD hi hj hne))

/-- The coefficient after removing the chosen normal direction and contracting
with the Euler vector in another slot. The two deleted coordinates contribute
their weights to balance precisely the differentials still in the wedge. -/
theorem radial_residue_entry (hG : G.IsWeightedHomogeneous geometricWeight 6)
    (hD : ∀ i p, D i (v p) = v (pderiv i p)) {j : Fin 5} (hj : j ∈ T)
    (hne : v (pderiv j G) ≠ 0) (r : Fin 5) {d : ℤ} {a : K} (ha : Rep d a) :
    Rep (d - 6 + weight j + weight r)
      ((a / D j F) * ((geometricWeight r : K) * v (X r))) := by
  have hx := Represented.polynomial v (denominators G T) (C (geometricWeight r : k) * X r)
    (geometricWeight r) ((isWeightedHomogeneous_X k geometricWeight r).C_mul _)
  have hc : v (C (geometricWeight r : k)) = (geometricWeight r : K) := by
    exact map_natCast (v.comp (C : k →+* P)) _
  rw [map_mul, hc] at hx
  exact (residue_entry hG hD hj hne ha).mul hx

end CycleQ2WeightedCechPresentations
end

#print axioms CycleQ2WeightedCechPresentations.vertex_numerator
#print axioms CycleQ2WeightedCechPresentations.edge_numerator
#print axioms CycleQ2WeightedCechPresentations.face_numerator
#print axioms CycleQ2WeightedCechPresentations.radial_residue_entry
