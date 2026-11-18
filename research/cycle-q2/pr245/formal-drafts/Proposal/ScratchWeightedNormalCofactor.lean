import Proposal.GeometricPoleReductionGradient
import Proposal.GeometricLogarithmicResidue
import Proposal.ScratchWeightedRadialExpansion
import Proposal.GeometricIncidenceChartMinor

/-!
# Ordinary residue on gradient patches and the weight of its cofactors

The localized normal vector evaluates dXᵢ as the inverse of the chosen
partial derivative and all other coordinate differentials as zero. Restriction
to the hypersurface after this insertion is the ordinary Poincaré residue
with dG in the first slot. Each coefficient of this residue has weight
opposite to the weight of its remaining coordinate differentials.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2WeightedNormalCofactor

open MvPolynomial
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2PoleReductionGradient (Poly partial partial_map normal)
open CycleQ2LiteralThreefoldResidueContraction (interior)
open CycleQ2WeightedChartShear (coordWedge exteriorWeight)
open CycleQ2WeightedRadialExpansion (insertedCoefficient interior_expansion_with exteriorWeight_remove)
open CycleQ2LogarithmicResidue (localResidue)
open CycleQ2LogarithmicPullback (differential differential_D)
open CycleQ2GeometricExteriorSheaf (exteriorMap exteriorMap_wedge)
open scoped KaehlerDifferential

variable {k R S T : Type} [CommRing k] [CommRing R] [CommRing S] [CommRing T]
  [Algebra k R] [Algebra k T]

/-- The normalized coordinate vector, recording only its nonzero evaluation. -/
def normalValue (i : Fin 5) (u : R) (j : Fin 5) : R := if j = i then u else 0

/-- Ordinary residue of a finite regular numerator, evaluated on the divisor. -/
theorem residue_expansion (q : R →ₐ[k] T) (D : Derivation k R R) (x v : Fin 5 → R)
    (hv : ∀ i, D (x i) = v i)
    {A : Type} (s : Finset A) (n : ℕ) (I : A → Fin (n+1) → Fin 5) (c : A → R) :
    localResidue q n D (∑ a ∈ s, c a • coordWedge (k := k) x (I a)) =
      ∑ p ∈ s.product (Finset.univ : Finset (Fin (n+1))),
        q (insertedCoefficient v (c p.1) (I p.1) p.2) •
          coordWedge (k := k) (q ∘ x) (p.2.removeNth (I p.1)) := by
  have h := interior_expansion_with D.liftKaehlerDifferential x v
    (fun j => (D.liftKaehlerDifferential_comp_D _).trans (hv j)) s n I c
  unfold localResidue CycleQ2LogarithmicResidue.residue
  rw [h,map_sum]
  apply Finset.sum_congr rfl
  intro p _
  rw [map_smulₛₗ]
  change q _ • exteriorMap q.toRingHom (differential q) n
    (coordWedge (k := k) x (p.2.removeNth (I p.1))) = _
  simp only [coordWedge, exteriorMap_wedge, differential_D, Function.comp_apply]

/-- The chart transition of an inverse gradient is the inverse transition
of its defining homogeneous polynomial, including its coordinate weight. -/
theorem normalValue_scale (π σ : R →+* S) (t : S) (i : Fin 5) (g u : R)
    (hu : g*u = 1) (hg : σ g = t^(6-geometricWeight i) * π g) (j : Fin 5) :
    σ (normalValue i u j) * t^6 = t^(geometricWeight j) * π (normalValue i u j) := by
  by_cases hji : j = i
  · subst j
    simp only [normalValue, if_pos rfl]
    have hπ : π g * π u = 1 := by rw [← map_mul, hu, map_one]
    have hσ : σ g * σ u = 1 := by rw [← map_mul, hu, map_one]
    have h' : σ u * t^(6-geometricWeight i) = π u := calc
      _ = (σ u * t^(6-geometricWeight i)) * (π g * π u) := by rw [hπ,mul_one]
      _ = (σ g * σ u) * π u := by rw [hg]; ring
      _ = π u := by rw [hσ,one_mul]
    have hw : 6-geometricWeight i + geometricWeight i = 6 :=
      Nat.sub_add_cancel (le_trans (CycleQ2IncidenceChartMinor.geometricWeight_le_two i) (by decide))
    calc
      σ u * t^6 = σ u * t^(6-geometricWeight i + geometricWeight i) := by rw [hw]
      _ = t^(geometricWeight i) * (σ u * t^(6-geometricWeight i)) := by rw [pow_add]; ring
      _ = _ := by rw [h']
  · simp [normalValue,hji]

/-- A weight-six ordinary logarithmic numerator gives a weight-zero residue.
All signs in a given cofactor are retained by both restrictions. -/
theorem residue_coefficient_scale (π σ : R →+* S) (t : S) (ht : IsUnit t)
    (i : Fin 5) (g u : R) (hu : g*u = 1) (hg : σ g = t^(6-geometricWeight i)*π g)
    {n : ℕ} (I : Fin (n+1) → Fin 5) (c : R)
    (hc : σ c * t^(exteriorWeight I) = t^6 * π c) (j : Fin (n+1)) :
    σ (insertedCoefficient (normalValue i u) c I j) * t^(exteriorWeight (j.removeNth I)) =
      π (insertedCoefficient (normalValue i u) c I j) := by
  let w := geometricWeight (I j)
  let m := exteriorWeight (j.removeNth I)
  let a := normalValue i u (I j)
  have hc' : σ c * (t^w * t^m) = t^6 * π c := by
    rw [← pow_add, ← exteriorWeight_remove I j]
    exact hc
  have ha : σ a * t^6 = t^w * π a := normalValue_scale π σ t i g u hu hg (I j)
  apply ((ht.pow 6).mul_left_inj).mp
  simp only [insertedCoefficient,map_mul,map_pow,map_neg,map_one]
  change (σ c * ((-1 : S)^j.val * σ a)) * t^m * t^6 =
    (π c * ((-1 : S)^j.val * π a)) * t^6
  calc
    _ = σ c * t^m * (-1 : S)^j.val * (σ a * t^6) := by ring
    _ = (σ c * (t^w * t^m)) * ((-1 : S)^j.val * π a) := by rw [ha]; ring
    _ = _ := by rw [hc']; ring

section Gradient

variable (M : Submonoid (Poly k))
local notation "B" => Localization M
local notation "ι" => algebraMap (Poly k) B

def inverseGradient (G : Poly k) (i : Fin 5) (hi : pderiv i G ∈ M) : B :=
  (↑(IsLocalization.map_units B (⟨pderiv i G, hi⟩ : M)).unit⁻¹ : B)

@[simp] theorem gradient_mul_inverse (G : Poly k) (i : Fin 5) (hi : pderiv i G ∈ M) :
    ι (pderiv i G) * inverseGradient M G i hi = 1 :=
  (IsLocalization.map_units B (⟨pderiv i G, hi⟩ : M)).unit.mul_inv

@[simp] theorem normal_coordinate (G : Poly k) (i : Fin 5) (hi : pderiv i G ∈ M) (j : Fin 5) :
    normal M G i hi (ι (X j)) = normalValue i (inverseGradient M G i hi) j := by
  change inverseGradient M G i hi * partial M i (ι (X j)) = _
  rw [partial_map]
  by_cases hji : j = i
  · subst j
    simp [normalValue]
  · simp [normalValue,hji,pderiv_X_of_ne hji]

/-- Ordinary residue on the actual localization with its normalized spatial
derivation. For the hypersurface take q to be its principal quotient map. -/
theorem gradient_residue (q : B →ₐ[k] T) (G : Poly k) (i : Fin 5) (hi : pderiv i G ∈ M)
    {A : Type} (s : Finset A) (n : ℕ) (I : A → Fin (n+1) → Fin 5) (c : A → B) :
    localResidue q n (normal M G i hi)
      (∑ a ∈ s, c a • coordWedge (k := k) (fun j => ι (X j)) (I a)) =
      ∑ p ∈ s.product (Finset.univ : Finset (Fin (n+1))),
        q (insertedCoefficient (normalValue i (inverseGradient M G i hi)) (c p.1) (I p.1) p.2) •
          coordWedge (k := k) (fun j => q (ι (X j))) (p.2.removeNth (I p.1)) :=
  residue_expansion q _ _ _ (normal_coordinate M G i hi) s n I c

/-- The actual quotient coefficient on each simplex has the degree-zero
transition required by the projective chart gluing theorem. -/
theorem gradient_residue_coefficient (q : B →ₐ[k] T) (π σ : T →+* S) (t : S) (ht : IsUnit t)
    (G : Poly k) (i : Fin 5) (hi : pderiv i G ∈ M)
    (hg : σ (q (ι (pderiv i G))) = t^(6-geometricWeight i) * π (q (ι (pderiv i G))))
    {n : ℕ} (I : Fin (n+1) → Fin 5) (c : B)
    (hc : σ (q c) * t^(exteriorWeight I) = t^6 * π (q c)) (j : Fin (n+1)) :
    σ (q (insertedCoefficient (normalValue i (inverseGradient M G i hi)) c I j)) *
      t^(exteriorWeight (j.removeNth I)) =
    π (q (insertedCoefficient (normalValue i (inverseGradient M G i hi)) c I j)) :=
  residue_coefficient_scale (π.comp q.toRingHom) (σ.comp q.toRingHom) t ht i
    (ι (pderiv i G)) (inverseGradient M G i hi) (gradient_mul_inverse M G i hi) hg I c hc j

end Gradient
end CycleQ2WeightedNormalCofactor
end

#print axioms CycleQ2WeightedNormalCofactor.gradient_residue
#print axioms CycleQ2WeightedNormalCofactor.gradient_residue_coefficient
