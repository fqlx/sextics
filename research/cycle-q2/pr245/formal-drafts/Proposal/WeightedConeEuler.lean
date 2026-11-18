import Proposal.ScratchWeightedPoleEuler
import Proposal.WeightedConePartial
import Proposal.WeightedConeVertex
import Mathlib.RingTheory.MvPolynomial.EulerIdentity

/-!
# Euler equations on the true weighted cone fraction field

The polynomial Euler identity and the fraction-field coordinate partials give
the radial degrees of every complementary component of the Čech cocycle.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedConeEuler

open MvPolynomial
open CycleQ2WeightedDoublePoleCech
open CycleQ2WeightedPoleEuler (HasWeight EulerCommutes radial)
open CycleQ2WeightedConePartial (RF value «partial» partial_map)
open CycleQ2WeightedConeVertex (coneNumerator)
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (equation)

variable {L : Type} [Field L] [CharZero L]
abbrev D := «partial» (ι := Fin 5) (k := L)
def weight (i : Fin 5) : ℤ := geometricWeight i
abbrev x (i : Fin 5) : RF (Fin 5) L := value (X i)
abbrev E := radial (D (L := L)) weight x

private theorem coordinate_partial (i j : Fin 5) :
    D (L := L) i (x j) = if i = j then 1 else 0 := by
  rw [x,D,partial_map]
  by_cases h : i=j
  · subst j
    simp only [pderiv_X_self,map_one,if_pos rfl]
  · rw [pderiv_X_of_ne h.symm,map_zero,if_neg h]

theorem euler_commutes : EulerCommutes (D (L := L)) weight E :=
  CycleQ2WeightedPoleEuler.radial_commutes D weight x coordinate_partial
    CycleQ2WeightedConePartial.partial_commute

theorem homogeneous_weight (p : MvPolynomial (Fin 5) L) (d : ℕ)
    (hp : p.IsWeightedHomogeneous geometricWeight d) : HasWeight E d (value p) := by
  change radial D weight x (value p) = _
  rw [CycleQ2WeightedPoleEuler.radial_apply]
  calc
    _ = value (∑ i : Fin 5, geometricWeight i • (X i * pderiv i p)) := by
      rw [map_sum]
      apply Finset.sum_congr rfl
      intro i hi
      simp only [weight,x,D,partial_map,Int.cast_natCast,map_nsmul,nsmul_eq_mul,map_mul,mul_assoc]
    _ = _ := by rw [hp.sum_weight_X_mul_pderiv,map_nsmul,nsmul_eq_mul,Int.cast_natCast]

theorem equation_weight (φ : CoeffRing →+* L) :
    HasWeight E 6 (value (equation φ)) :=
  homogeneous_weight _ 6 (CycleQ2GeometricHodgeThreefold.equation_homogeneous φ)

theorem numerator_homogeneous : (coneNumerator L).IsWeightedHomogeneous geometricWeight 12 := by
  have h (i : Fin 5) := (isWeightedHomogeneous_X L geometricWeight i).pow 2
  exact ((((h 0).mul (h 1)).mul (h 2)).mul (h 3)).mul (h 4)

theorem numerator_weight : HasWeight E 12 (value (coneNumerator L)) :=
  homogeneous_weight _ 12 numerator_homogeneous

theorem simplex_weights (φ : CoeffRing →+* L) (i j l a c : Fin 5) :
    HasWeight E (-6) (vertex D (value (equation φ)) (value (coneNumerator L)) i) ∧
    HasWeight E (-6+weight a) (edge D (value (equation φ)) (value (coneNumerator L)) i j a) ∧
    HasWeight E (-6+weight a+weight c)
      (face D (value (equation φ)) (value (coneNumerator L)) i j l a c) :=
  ⟨CycleQ2WeightedPoleEuler.vertex_weight D weight euler_commutes
      (equation_weight φ) numerator_weight i,
   CycleQ2WeightedPoleEuler.edge_weight D weight euler_commutes
      (equation_weight φ) numerator_weight i j a,
   CycleQ2WeightedPoleEuler.face_weight D weight euler_commutes
      (equation_weight φ) numerator_weight i j l a c⟩

end CycleQ2WeightedConeEuler
end
#print axioms CycleQ2WeightedConeEuler.simplex_weights
