import Proposal.ScratchLogCofactor
import Proposal.ScratchLogInteriorAnti

/-!
# Euler weights of the exterior cofactors of a volume

The endomorphism summing weighted left multiplication followed by
contraction counts the total weight of the differentials in a coordinate
wedge. Each omitted coordinate subtracts its weight, in every degree.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogCofactorWeight

open CycleQ2LogBasisConnection CycleQ2LogCofactor CycleQ2LogarithmicDifferential
open CycleQ2LiteralThreefoldResidueContraction (interior)
open CycleQ2LogInteriorAnti (interior_swap)
open CycleQ2PoleReductionLocal (prepend contract_prepend top_wedge)

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]
variable {I : Type} [Fintype I] [LinearOrder I]
variable (b : Module.Basis I R (KaehlerDifferential k R)) (w : I → R)

def degreeOperator (n : ℕ) : Form k R (n+1) →ₗ[R] Form k R (n+1) :=
  ∑ i, w i • (prepend n (b i)).comp (interior n (b.coord i))

theorem degreeOperator_apply (n : ℕ) (ω : Form k R (n+1)) :
    degreeOperator b w n ω = ∑ i, w i • prepend n (b i) (interior n (b.coord i) ω) := by
  simp only [degreeOperator, LinearMap.sum_apply, LinearMap.smul_apply, LinearMap.comp_apply]

private theorem delta (i j : I) : b.coord i (b j) = if j = i then 1 else 0 :=
  b.repr_self_apply j i

/-- A coordinate contraction subtracts its own weight. -/
theorem degreeOperator_interior (n : ℕ) (j : I) (ω : Form k R (n+2)) :
    degreeOperator b w n (interior (n+1) (b.coord j) ω) =
      interior (n+1) (b.coord j) (degreeOperator b w (n+1) ω) -
        w j • interior (n+1) (b.coord j) ω := by
  classical
  rw [degreeOperator_apply, degreeOperator_apply, map_sum]
  have step (i : I) :
      interior (n+1) (b.coord j) (w i • prepend (n+1) (b i) (interior (n+1) (b.coord i) ω)) =
        (if i = j then w i • interior (n+1) (b.coord i) ω else 0) +
        w i • prepend n (b i) (interior n (b.coord i) (interior (n+1) (b.coord j) ω)) := by
    rw [map_smul, contract_prepend, interior_swap n (b.coord j) (b.coord i), map_neg,
      sub_neg_eq_add, smul_add, delta]
    by_cases h : i = j <;> simp [h]
  simp_rw [step]
  rw [Finset.sum_add_distrib]
  simp

/-- A coordinate tensor independent of the spatial variables together with
its exterior Euler weight. -/
def ConstantWeight (n : ℕ) (weight : R) (ω : Form k R (n+1)) : Prop :=
  (∀ i : I, coeffD (b.exteriorPower (n+1)) (coordDeriv b i) ω = 0) ∧
    degreeOperator b w n ω = weight • ω

theorem constantWeight_interior (n : ℕ) (j : I) {weight : R} {ω : Form k R (n+2)}
    (h : ConstantWeight b w (n+1) weight ω) :
    ConstantWeight b w n (weight - w j) (interior (n+1) (b.coord j) ω) := by
  refine ⟨fun i => ?_, ?_⟩
  · rw [coeffD_interior, h.1 i, map_zero]
  · rw [degreeOperator_interior, h.2, map_smul, sub_smul]

theorem constantWeight_volume (B : Module.Basis (Fin 5) R (KaehlerDifferential k R))
    (W : Fin 5 → R) : ConstantWeight B W 4 (∑ i, W i) (volume B) := by
  constructor
  · intro i
    exact coeffD_wedge_basis B 5 (coordDeriv B i) id
  · rw [degreeOperator_apply, Finset.sum_smul]
    apply Finset.sum_congr rfl
    intro i _
    rw [top_wedge B, delta, if_pos rfl, one_smul]

/-- The coefficient-derivative and exterior-degree terms of Euler's action
on a scalar times a constant tensor combine as in the homogeneous Euler formula. -/
theorem euler_scalar (n : ℕ) {weight : R} {ω : Form k R (n+1)}
    (h : ConstantWeight b w n weight ω) (x : I → R) (a : R) :
    (∑ i, (w i * x i) • coeffD (b.exteriorPower (n+1)) (coordDeriv b i) (a • ω)) +
      degreeOperator b w n (a • ω) =
      (∑ i, (w i * x i) * coordDeriv b i a) • ω + weight • (a • ω) := by
  simp only [coeffD_smul, h.1, smul_zero, add_zero, map_smul, h.2, smul_smul,
    Finset.sum_smul, mul_comm a weight]

end CycleQ2LogCofactorWeight
end
#print axioms CycleQ2LogCofactorWeight.degreeOperator_interior
#print axioms CycleQ2LogCofactorWeight.constantWeight_volume
#print axioms CycleQ2LogCofactorWeight.euler_scalar
