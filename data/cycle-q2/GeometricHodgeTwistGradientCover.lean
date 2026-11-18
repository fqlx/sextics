import Proposal.GeometricHodgeEulerSheafCoefficients
import Proposal.GeometricHodgeThreefoldProper

/-!
# Four projective opens carrying invertible normal derivatives

On the existing gradient-minor open, a power of every coordinate belongs
to the ideal of the five Euler products. On the hypersurface the weighted
Euler relation expresses twice the fifth product using the first four.
Thus the four basic opens of xᵢ ∂ᵢF cover the actual moving Proj.
At the Fermat point these are exactly the original weight-one charts.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeTwistGradientCover
open AlgebraicGeometry CategoryTheory TopologicalSpace MvPolynomial
open CycleQ2GeometricHodgeThreefold
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2HodgeEulerSheaf (partialValue partial_mem)
open CycleQ2GenericSexticGradient (CoeffRing seedEvaluation gradientOpen coordinate_power_mem generators coordinatePower)
open CycleQ2HomogeneousIdealArithmetic (generatorIdeal)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

def product (j : Fin 5) : cone φ := coord φ j * partialValue φ j

def pivotOpen (i : Fin 4) : (threefold φ).Opens := Proj.basicOpen (grade φ) (product φ i.castSucc)

theorem pivotOpen_eq (i : Fin 4) : pivotOpen φ i = coordinateOpen φ i ⊓
    Proj.basicOpen (grade φ) (partialValue φ i.castSucc) :=
  Proj.basicOpen_mul (grade φ) _ _

theorem pivotOpen_le (i : Fin 4) : pivotOpen φ i ≤ coordinateOpen φ i := by
  rw [pivotOpen_eq]; exact inf_le_left

private theorem product_eq (j : Fin 5) : quotient φ (MvPolynomial.map φ (generators j)) = product φ j := by
  simp only [generators, map_mul, map_X, ← pderiv_map]
  rfl

private theorem euler : (∑ j : Fin 5, geometricWeight j • product φ j) = 0 := by
  have h := congrArg (quotient φ) ((equation_homogeneous φ).sum_weight_X_mul_pderiv)
  simpa only [map_sum, map_nsmul, map_mul, equation_zero, nsmul_zero, product, coord, partialValue] using h

def pivotIdeal : Ideal (cone φ) := Ideal.span (Set.range fun i : Fin 4 => product φ i.castSucc)

private theorem mem_pivotIdeal (j : Fin 5) : product φ j ∈ pivotIdeal φ := by
  induction j using Fin.lastCases with
  | cast i => exact Ideal.subset_span ⟨i,rfl⟩
  | last =>
    let Q := Ideal.Quotient.mk (pivotIdeal φ)
    let c : ℂ →+* (cone φ ⧸ pivotIdeal φ) := Q.comp ((quotient φ).comp (C.comp (φ.comp C)))
    have hu : IsUnit (2 : cone φ ⧸ pivotIdeal φ) := by
      simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (show (2 : ℂ) ≠ 0 by norm_num)).map c
    have he := congrArg Q (euler φ)
    rw [Fin.sum_univ_castSucc, map_add, map_sum, map_nsmul, map_zero] at he
    have hzero (i : Fin 4) : Q (geometricWeight i.castSucc • product φ i.castSucc) = 0 := by
      rw [map_nsmul, show Q (product φ i.castSucc) = 0 from Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩), nsmul_zero]
    rw [Finset.sum_eq_zero (fun i _ => hzero i), zero_add, nsmul_eq_mul] at he
    change (2 : cone φ ⧸ pivotIdeal φ) * Q (product φ (Fin.last 4)) = 0 at he
    exact Ideal.Quotient.eq_zero_iff_mem.mp (hu.mul_left_cancel (he.trans (mul_zero _).symm))

theorem coordinate_power_mem_pivots (hg : IsUnit (φ gradientOpen)) (j : Fin 5) :
    (coord φ j)^coordinatePower j ∈ pivotIdeal φ := by
  have hI : generatorIdeal (fun i => MvPolynomial.map φ (generators i)) ≤
      (pivotIdeal φ).comap (quotient φ) := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    exact (product_eq φ i).symm ▸ mem_pivotIdeal φ i
  have hp := hI (coordinate_power_mem φ hg j)
  change quotient φ ((X j)^coordinatePower j) ∈ _ at hp
  simpa only [map_pow, coord] using hp

theorem cover (hg : IsUnit (φ gradientOpen)) : (⨆ i : Fin 4, pivotOpen φ i) = ⊤ := by
  apply top_le_iff.mp
  intro q _
  apply Opens.mem_iSup.mpr
  classical
  by_contra hn
  let P := q.asHomogeneousIdeal.toIdeal
  letI : P.IsPrime := q.isPrime
  have hle : pivotIdeal φ ≤ P := by
    apply Ideal.span_le.mpr
    rintro _ ⟨i,rfl⟩
    by_contra h
    exact hn ⟨i,h⟩
  apply q.not_irrelevant_le
  apply (irrelevant_le_coordinateIdeal φ).trans
  apply Ideal.span_le.mpr
  rintro _ ⟨j,rfl⟩
  exact Ideal.IsPrime.mem_of_pow_mem inferInstance (coordinatePower j) (hle (coordinate_power_mem_pivots φ hg j))

theorem seed_product (i : Fin 4) : product seedEvaluation i.castSucc = 6 * coord seedEvaluation i.castSucc ^ 6 := by
  rw [← product_eq, CycleQ2GenericSexticGradient.generators_seed, map_mul, map_pow]
  have hs : CycleQ2FermatJacobian.derivativeScalar i.castSucc = 6 := by fin_cases i <;> rfl
  have hp : CycleQ2GenericSexticGradient.purePower i.castSucc = 6 := by fin_cases i <;> rfl
  simp only [hs, hp, map_ofNat, coord]

theorem seed_pivotOpen (i : Fin 4) : pivotOpen seedEvaluation i = coordinateOpen seedEvaluation i := by
  have hu : IsUnit (6 : cone seedEvaluation) := by
    let c : ℂ →+* cone seedEvaluation := (quotient seedEvaluation).comp C
    simpa only [map_ofNat] using (isUnit_iff_ne_zero.mpr (show (6 : ℂ) ≠ 0 by norm_num)).map c
  rw [pivotOpen, seed_product, Proj.basicOpen_mul, Proj.basicOpen_pow _ _ 6 (by decide)]
  apply le_antisymm inf_le_right
  refine le_inf ?_ le_rfl
  intro q _
  exact fun h => q.isPrime.ne_top ((Ideal.eq_top_of_isUnit_mem _ h hu))

end CycleQ2HodgeTwistGradientCover
end
#print axioms CycleQ2HodgeTwistGradientCover.coordinate_power_mem_pivots
#print axioms CycleQ2HodgeTwistGradientCover.cover
#print axioms CycleQ2HodgeTwistGradientCover.seed_pivotOpen
