import Proposal.GeometricGenericWeightedMonicCoefficients
import Proposal.GeometricMonicWeightedAffineEquation

/-!
# The monic spatial cubic over the deformed parameter field

The three spatial coordinates and both parameters generate a field over
which the remaining squared coordinate satisfies the normalized sextic,
viewed as its monic cubic in the final variable.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2GenericWeightedSpatialCubic

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2GenericSpecialization
  CycleQ2GenericPencilLift CycleQ2GenericWeightedCoordinates CycleQ2GenericWeightedMonicCoefficients
open CycleQ2GenericWeightedOpen (coefficientPoint)
open CycleQ2GenericWeightedMonicOpen (normalizedCoefficientPoint equation_eq_leading_mul_normalized)
open CycleQ2GenericWeightedPencilEquation (weightedPoint endpoint_equation)
open CycleQ2GeometricHodgeThreefoldCubic (baseValue expand)

/-- Parameters and three spatial coordinates, inside the actual ambient rational field. -/
def parameters (d : Direction) : Fin 5 → RF := ![parameter d, lambda, z 0, z 2, z 3]

abbrev spatialField (d : Direction) := IntermediateField.adjoin ℂ (Set.range (parameters d))

theorem parameter_mem (d : Direction) (i : Fin 5) : parameters d i ∈ spatialField d :=
  IntermediateField.subset_adjoin ℂ _ (Set.mem_range_self i)

theorem coefficientField_le (d : Direction) : coefficientField d ≤ spatialField d := by
  apply IntermediateField.adjoin_le_iff.mpr
  intro x hx
  rcases Set.mem_insert_iff.mp hx with h | h
  · exact h ▸ parameter_mem d 0
  · exact (Set.mem_singleton_iff.mp h) ▸ parameter_mem d 1

/-- Evaluation of the univariate expansion at the remaining weight-two coordinate. -/
private theorem eval_cubic {A K : Type} [CommRing A] [Field K] [Algebra A K]
    (x : Fin 3 → A) (s : K) (p : MvPolynomial (Fin 5) A) :
    Polynomial.eval₂ (algebraMap A K) s
      ((expand 0 p).map (eval x)) =
        eval₂Hom (algebraMap A K) ![1, algebraMap A K (x 0), algebraMap A K (x 1),
          algebraMap A K (x 2), s] p := by
  let φ := (Polynomial.eval₂RingHom (algebraMap A K) s).comp
    ((Polynomial.mapRingHom (eval x)).comp (expand 0).toRingHom)
  have he : φ = eval₂Hom (algebraMap A K) ![1, algebraMap A K (x 0), algebraMap A K (x 1),
      algebraMap A K (x 2), s] := by
    apply MvPolynomial.ringHom_ext
    · intro a
      change Polynomial.eval₂ (algebraMap A K) s ((expand 0 (C a)).map (eval x)) = _
      rw [expand, aeval_C, eval₂Hom_C]
      change Polynomial.eval₂ (algebraMap A K) s ((Polynomial.C (C a : MvPolynomial (Fin 3) A)).map (eval x)) = algebraMap A K a
      simp
    · intro i
      change Polynomial.eval₂ (algebraMap A K) s ((expand 0 (X i)).map (eval x)) = _
      rw [expand, aeval_X, eval₂Hom_X']
      fin_cases i
      all_goals first
        | change Polynomial.eval₂ (algebraMap A K) s ((Polynomial.C (1 : MvPolynomial (Fin 3) A)).map (eval x)) = 1
          simp
        | change Polynomial.eval₂ (algebraMap A K) s ((Polynomial.C (X _ : MvPolynomial (Fin 3) A)).map (eval x)) = algebraMap A K (x _)
          simp
        | change Polynomial.eval₂ (algebraMap A K) s ((Polynomial.X : Polynomial (MvPolynomial (Fin 3) A)).map (eval x)) = s
          simp
        | simp [φ, expand, baseValue, Fin.snoc]
      all_goals rfl
  exact RingHom.congr_fun he p

private theorem integral_of_normalized {A K : Type} [Field A] [Field K] [Algebra A K]
    (x : Fin 3 → A) (s : K) (h : FullSexticTailIndex → A)
    (he : eval₂Hom (algebraMap A K) ![1, algebraMap A K (x 0), algebraMap A K (x 1),
      algebraMap A K (x 2), s] (normalizedFullSextic h) = 0) : IsIntegral A s := by
  let p := CycleQ2MonicWeightedAffineEquation.equation h
  refine ⟨p.map (eval x), (CycleQ2MonicWeightedAffineEquation.monic h).map _, ?_⟩
  exact (eval_cubic x s (normalizedFullSextic h)).trans he

variable (c : FullInvariantIndex 6 → ℂ) (hc : endpointDifference c ≠ 0)

theorem square_integral
    (hL : coefficientPoint (endpointDirection c hc) c fullSexticLeadingIndex ≠ 0) :
    IsIntegral (spatialField (endpointDirection c hc)) (u ^ 2) := by
  let d := endpointDirection c hc
  let F := spatialField d
  let x : Fin 3 → F := ![⟨z 0, parameter_mem d 2⟩, ⟨z 2, parameter_mem d 3⟩,
    ⟨z 3, parameter_mem d 4⟩]
  let h : FullSexticTailIndex → F := fun e =>
    ⟨_, coefficientField_le d (coefficients d c e).property⟩
  apply integral_of_normalized x (u ^ 2) h
  change eval₂Hom (algebraMap F RF) weightedPoint (normalizedFullSextic h) = 0
  rw [show eval₂Hom (algebraMap F RF) weightedPoint (normalizedFullSextic h) =
    eval weightedPoint (MvPolynomial.map (algebraMap F RF) (normalizedFullSextic h)) from
    MvPolynomial.eval₂_eq_eval_map ..]
  have hmap : MvPolynomial.map (algebraMap F RF) (normalizedFullSextic h) =
      normalizedFullSextic (normalizedCoefficientPoint d c) := by
    simp only [normalizedFullSextic, map_add, map_sum, map_monomial, map_one]
    rfl
  rw [hmap]
  have hz := endpoint_equation c hc
  rw [equation_eq_leading_mul_normalized _ _ hL, map_mul, eval_C] at hz
  exact (mul_eq_zero.mp hz).resolve_left hL

theorem u_integral
    (hL : coefficientPoint (endpointDirection c hc) c fullSexticLeadingIndex ≠ 0) :
    IsIntegral (spatialField (endpointDirection c hc)) u :=
  IsIntegral.of_pow (by decide : 0 < 2) (square_integral c hc hL)

end CycleQ2GenericWeightedSpatialCubic
end

#print axioms CycleQ2GenericWeightedSpatialCubic.u_integral
