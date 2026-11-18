import Proposal.GeometricIncidenceChartMinor
import Mathlib.RingTheory.Localization.Away.Basic

/-! The common denominator monoids of the homogeneous cone gradient charts.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedCechPresentations
open MvPolynomial CycleQ2GeometricIncidenceProj
variable {k : Type} [CommRing k]
local notation "P" => MvPolynomial (Fin 5) k

/-- The denominator monoid on an intersection of homogeneous derivative opens. -/
def denominators (G : P) (T : Set (Fin 5)) : Submonoid P :=
  Submonoid.closure ((fun j => pderiv j G) '' T)

theorem derivative_mem (G : P) {T : Set (Fin 5)} {i : Fin 5} (hi : i ∈ T) :
    pderiv i G ∈ denominators G T := Submonoid.subset_closure ⟨i,hi,rfl⟩

/-- Each denominator is itself homogeneous for the original cone action. -/
theorem denominators_homogeneous {G : P} (hG : G.IsWeightedHomogeneous geometricWeight 6)
    (T : Set (Fin 5)) (q : denominators G T) :
    ∃ n : ℕ, (q : P).IsWeightedHomogeneous geometricWeight n := by
  obtain ⟨q,hq⟩ := q
  change q ∈ Submonoid.closure _ at hq
  change ∃ n : ℕ, q.IsWeightedHomogeneous geometricWeight n
  induction hq using Submonoid.closure_induction with
  | mem q h =>
    obtain ⟨j,hj,rfl⟩ := h
    refine ⟨6 - geometricWeight j,?_⟩
    intro e he
    rw [MvPolynomial.coeff_pderiv] at he
    have hc : coeff (e + Finsupp.single j 1) G ≠ 0 := by
      intro hz
      exact he (by rw [hz, zero_mul])
    have hd := hG hc
    simp only [map_add, Finsupp.weight_single, one_smul] at hd
    omega
  | one => exact ⟨0,isWeightedHomogeneous_one _ _⟩
  | mul x y hx hy hx' hy' =>
    obtain ⟨a,ha⟩ := hx'
    obtain ⟨b,hb⟩ := hy'
    exact ⟨a+b,ha.mul hb⟩

/-- Inverting the listed derivatives in any chart algebra inverts exactly the
allowed products used in the normalized Čech coefficients. -/
theorem denominators_map_units {V : Type*} [CommRing V] (G : P)
    (T : Set (Fin 5)) (f : P →+* V) (h : ∀ i ∈ T, IsUnit (f (pderiv i G)))
    (q : denominators G T) : IsUnit (f q) := by
  obtain ⟨q,hq⟩ := q
  change q ∈ Submonoid.closure _ at hq
  change IsUnit (f q)
  induction hq using Submonoid.closure_induction with
  | mem q hq =>
    obtain ⟨i,hi,rfl⟩ := hq
    exact h i hi
  | one => simp
  | mul x y hx hy hx' hy' => simpa only [map_mul] using hx'.mul hy'

/-- Every allowed denominator is a unit in the ordinary principal localization
at the product of the derivatives indexed by the finite intersection. -/
theorem denominators_are_units (G : P) (T : Finset (Fin 5)) (q : P)
    (hq : q ∈ denominators G (T : Set (Fin 5))) :
    IsUnit (algebraMap P (Localization.Away (∏ i ∈ T, pderiv i G)) q) :=
  denominators_map_units G (T : Set (Fin 5)) _
    (fun i hi => IsLocalization.Away.isUnit_of_dvd _ (Finset.dvd_prod_of_mem (fun j : Fin 5 => pderiv j G) (show i ∈ T from hi)))
    ⟨q,hq⟩

end CycleQ2WeightedCechPresentations
end

#print axioms CycleQ2WeightedCechPresentations.denominators_homogeneous
#print axioms CycleQ2WeightedCechPresentations.denominators_map_units
