import Proposal.GeometricHodgeEulerTangentValues
import Proposal.GeometricHodgeEulerTangentCoordinates

/-! On every subopen of a weight-one chart, the five intrinsic
derivatives of the normalized homogeneous coordinates form a linear
map to the actual Jacobian kernel with zero pivot coordinate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerTangentToQuotient

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold coord coord_mem_grade toBase)
open CycleQ2HodgeTwistRatios (normalized U)
open CycleQ2HodgeEulerSheaf
open CycleQ2HodgeEulerTangentSheaf CycleQ2HodgeEulerTangentValues CycleQ2HodgeEulerTangentCoordinates
open CycleQ2HodgeEuler (pairing pairing_apply coordinate)

variable (φ : CoeffRing →+* ℂ) (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i)

abbrev coordinateSection (j : Fin 5) := normalized φ i (coord φ j) (coord_mem_grade φ j) V hi

def values (s : Γ(tangent (toBase φ),V)) (j : Fin 5) :=
  sectionD (toBase φ) s (coordinateSection φ i V hi j)

theorem pivot_zero (s : Γ(tangent (toBase φ),V)) : values φ i V hi s i.castSucc = 0 := by
  let := nativeAlgebra (toBase φ) V
  have h := (chartSection_coordinate φ i V hi i.castSucc).symm
  simp only [coordinate, CycleQ2HodgeEuler.dehom_X_self, map_one] at h
  unfold values
  change sectionD (toBase φ) s (normalized φ i _ _ V hi) = 0
  rw [h, Derivation.map_one_eq_zero]

theorem tangent_equation (s : Γ(tangent (toBase φ),V)) :
    pairing (fun j => normalized φ i (partialValue φ j) (partial_mem φ j) V hi) (values φ i V hi s) = 0 := by
  rw [pairing_apply, Fin.sum_univ_succAbove _ i.castSucc, pivot_zero, mul_zero, zero_add]
  have h := section_gradient φ i V hi s
  refine Eq.trans (Finset.sum_congr rfl fun j _ => ?_) h
  have h₁ := chartSection_partial φ i V hi (i.castSucc.succAbove j)
  rw [CycleQ2HodgeEuler.partial_succAbove] at h₁
  have h₂ := chartSection_coordinate φ i V hi (i.castSucc.succAbove j)
  rw [CycleQ2HodgeEuler.coordinate, CycleQ2HodgeEuler.dehom_X_succAbove] at h₂
  exact congrArg₂ (· * ·) h₁.symm (congrArg (sectionD (toBase φ) s) h₂.symm)

def valuesLinear : Γ(tangent (toBase φ),V) →ₗ[Γ(threefold φ,V)] (Fin 5 → Γ(threefold φ,V)) where
  toFun := values φ i V hi
  map_add' _ _ := rfl
  map_smul' a s := by
    funext j
    change (threefold φ).presheaf.map (𝟙 V).op a * values φ i V hi s j = a * values φ i V hi s j
    exact congrArg (· * values φ i V hi s j) (ConcreteCategory.congr_hom ((threefold φ).presheaf.map_id (op V)) a)

end CycleQ2HodgeEulerTangentToQuotient
end

#print axioms CycleQ2HodgeEulerTangentToQuotient.tangent_equation
#print axioms CycleQ2HodgeEulerTangentToQuotient.valuesLinear
