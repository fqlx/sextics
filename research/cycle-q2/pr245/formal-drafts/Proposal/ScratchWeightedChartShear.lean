import Proposal.GeometricHodgeEulerContractionTransition
import Proposal.GeometricExteriorSheaf

/-!
# Changes of variable on homogeneous horizontal differential forms

The relative differential of a normalized cone coordinate is its scaled
differential together with one multiple of the logarithmic differential of
the pivot. Removing that summand gives a semilinear map whose action on
every weighted wedge is a product of the coordinate powers.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedChartShear
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2GeometricExteriorSheaf (exteriorMap exteriorMap_wedge)
open scoped KaehlerDifferential

variable {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]
variable {M N : Type} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module S N]

/-- The component of the coordinate differential in the moving radial direction. -/
def axial (π : R →+* S) (l : M →ₗ[R] R) (a : N) : M →ₛₗ[π] N where
  toFun m := π (l m) • a
  map_add' x y := by rw [map_add, map_add, add_smul]
  map_smul' x m := by
    change π (l (x • m)) • a = π x • (π (l m) • a)
    rw [map_smul, smul_eq_mul, map_mul, mul_smul]

/-- Exact differential of a moving weighted coordinate, with its logarithmic part explicit. -/
theorem weighted_differential (t u v : S) (ht : t*u = 1) (n : ℕ) :
    KaehlerDifferential.D k S (t^n*v) =
      t^n • KaehlerDifferential.D k S v +
        ((n:S)*(t^n*v)) • (u • KaehlerDifferential.D k S t) := by
  cases n with
  | zero => simp
  | succ n =>
    rw [Derivation.leibniz, Derivation.leibniz_pow]
    simp only [Nat.add_sub_cancel, ← Nat.cast_smul_eq_nsmul S, smul_smul]
    congr 2
    rw [pow_succ]
    calc
      _ = ((n+1:S)*t^n*v)*(t*u) := by rw [ht, mul_one]; push_cast; ring
      _ = _ := by push_cast; ring

/-- Wedges of normalized differentials in a graded cone section. -/
def coordWedge {m : ℕ} (x : Fin 5 → R) (I : Fin m → Fin 5) :
    ⋀[R]^m Ω[R⁄k] := exteriorPower.ιMulti R m (fun j => KaehlerDifferential.D k R (x (I j)))

def exteriorWeight {m : ℕ} (I : Fin m → Fin 5) : ℕ := ∑ j, geometricWeight (I j)

/-- Apply a semilinear map with prescribed effects on weighted coordinates to a coordinate wedge. -/
theorem scaled_wedge (π : R →+* S) (L : Ω[R⁄k] →ₛₗ[π] Ω[S⁄k])
    (x : Fin 5 → R) (y : Fin 5 → S) (t : S)
    (hL : ∀ j, L (KaehlerDifferential.D k R (x j)) =
      t^(geometricWeight j) • KaehlerDifferential.D k S (y j)) {m : ℕ} (I : Fin m → Fin 5) :
    exteriorMap π L m (coordWedge (k := k) x I) =
      t^(exteriorWeight I) • coordWedge (k := k) y I := by
  simp only [coordWedge, exteriorMap_wedge, hL]
  rw [AlternatingMap.map_smul_univ, Finset.prod_pow_eq_pow_sum]

variable (π σ : R →ₐ[k] S) (L : Ω[R⁄k] →ₛₗ[σ.toRingHom] Ω[S⁄k])
  (l : Ω[R⁄k] →ₗ[R] R) (t u : S)
def frozen : Ω[R⁄k] →ₛₗ[σ.toRingHom] Ω[S⁄k] :=
  L - axial σ.toRingHom l (u • KaehlerDifferential.D k S t)

theorem moving_eq_frozen (m : Ω[R⁄k]) :
    L m = frozen σ L l t u m + σ (l m) • (u • KaehlerDifferential.D k S t) := by
  exact (sub_add_cancel _ _).symm

theorem frozen_D (ht : t * u = 1) (x : Fin 5 → R)
    (hσ : ∀ j, σ (x j) = t^(geometricWeight j) * π (x j))
    (hL : ∀ j, L (KaehlerDifferential.D k R (x j)) = KaehlerDifferential.D k S (σ (x j)))
    (hl : ∀ j, l (KaehlerDifferential.D k R (x j)) = (geometricWeight j:R)*x j) (j : Fin 5) :
    frozen σ L l t u (KaehlerDifferential.D k R (x j)) =
      t^(geometricWeight j) • KaehlerDifferential.D k S (π (x j)) := by
  change L _ - σ (l _) • _ = _
  rw [hL, hl, map_mul, map_natCast, hσ, weighted_differential (k := k) t u _ ht, add_sub_cancel_right]

/-- The frozen restriction and the restriction in the old coordinates agree on
the full finite expansion whenever each coefficient has the compensating weight. -/
theorem frozen_sum (H : Ω[R⁄k] →ₛₗ[π.toRingHom] Ω[S⁄k])
    (ht : t * u = 1) (x : Fin 5 → R)
    (hσ : ∀ j, σ (x j) = t^(geometricWeight j) * π (x j))
    (hL : ∀ j, L (KaehlerDifferential.D k R (x j)) = KaehlerDifferential.D k S (σ (x j)))
    (hH : ∀ j, H (KaehlerDifferential.D k R (x j)) = KaehlerDifferential.D k S (π (x j)))
    (hl : ∀ j, l (KaehlerDifferential.D k R (x j)) = (geometricWeight j:R)*x j)
    {ι : Type} (s : Finset ι) {m : ℕ} (I : ι → Fin m → Fin 5) (c : ι → R)
    (hc : ∀ a ∈ s, σ (c a)*t^(exteriorWeight (I a)) = π (c a)) :
    exteriorMap σ.toRingHom (frozen σ L l t u) m (∑ a ∈ s, c a • coordWedge (k := k) x (I a)) =
      exteriorMap π.toRingHom H m (∑ a ∈ s, c a • coordWedge (k := k) x (I a)) := by
  rw [map_sum,map_sum]
  apply Finset.sum_congr rfl
  intro a ha
  simp only [map_smulₛₗ]
  rw [scaled_wedge σ.toRingHom (frozen σ L l t u) x (π ∘ x) t (frozen_D π σ L l t u ht x hσ hL hl),
    smul_smul]
  change (σ (c a)*t^(exteriorWeight (I a))) • _ = _
  rw [hc a ha, coordWedge, exteriorMap_wedge]
  simp only [hH]
  rfl

end CycleQ2WeightedChartShear
end
#print axioms CycleQ2WeightedChartShear.frozen_sum
