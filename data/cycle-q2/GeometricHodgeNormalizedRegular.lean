import Proposal.GeometricLiteralAmbientCubicRegular
import Proposal.GeometricHodgeThreefoldIncidence
import Proposal.GeometricHodgeTwistRatios

/-!
# Regularity of the normalized cubic section

On every subopen of a weight-one chart, the normalized homogeneous section at a prime
has numerator the original cone element. Regularity survives localization at that prime
and multiplication by the inverse of the chart coordinate.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2HodgeNormalizedRegular

open AlgebraicGeometry HomogeneousLocalization CycleQ2GeometricHodgeThreefold
  CycleQ2GeometricHodgeThreefoldIncidence CycleQ2HodgeTwistRatios
  CycleQ2GeometricIncidenceProj CycleQ2IncidencePolynomialJacobianBinding
open CycleQ2GenericSexticGradient (CoeffRing)

private theorem fraction_regular {A : Type} [CommRing A] (M : Submonoid A) (p : A)
    (h : p ∈ nonZeroDivisors A) (d : M) :
    Localization.mk p d ∈ nonZeroDivisors (Localization M) := by
  have ha : algebraMap A (Localization M) p ∈ nonZeroDivisors (Localization M) :=
    IsLocalization.nonZeroDivisors_le_comap M (Localization M) h
  have hb := isRegular_iff_mem_nonZeroDivisors.mpr ha
  rw [← IsLocalization.mk'_spec (Localization M) p d] at hb
  rw [Localization.mk_eq_mk', ← isRegular_iff_mem_nonZeroDivisors]
  exact hb.of_mul_left

theorem normalized_regular {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Fin 4)
    {n : ℕ} (p : cone φ) (hp : p ∈ grade φ n) (hr : p ∈ nonZeroDivisors (cone φ))
    (V : (threefold φ).Opens) (hi : V ≤ coordinateOpen φ i) :
    normalized φ i p hp V hi ∈ nonZeroDivisors Γ(threefold φ, V) := by
  apply mem_nonZeroDivisors_iff_left.mpr
  intro s hs
  apply Subtype.ext
  funext q
  apply HomogeneousLocalization.val_injective
  let M := q.val.asHomogeneousIdeal.toIdeal.primeCompl
  let d : M := ⟨coord φ i.castSucc, hi q.property⟩
  change (s.val q).val = (0 : HomogeneousLocalization (grade φ) M).val
  rw [HomogeneousLocalization.val_zero]
  have hz := congrArg (fun z : Γ(threefold φ, V) => (z.val q).val) hs
  change (((normalized φ i p hp V hi).val q) * (s.val q)).val =
    (0 : HomogeneousLocalization (grade φ) M).val at hz
  rw [HomogeneousLocalization.val_mul, HomogeneousLocalization.val_zero] at hz
  change Localization.mk p (d ^ n) * (s.val q).val = 0 at hz
  exact mem_nonZeroDivisors_iff_left.mp (fraction_regular M p hr (d ^ n)) _ hz

private abbrev seed := seedPoint (57 : ℂ) Complex.I

theorem seed_cone_regular :
    quotient (sexticEval seed) (pointEquationH seed) ∈ nonZeroDivisors (cone (sexticEval seed)) := by
  change Ideal.Quotient.mk (Ideal.span {equation (sexticEval seed)}) _ ∈
    nonZeroDivisors (_ ⧸ Ideal.span {equation (sexticEval seed)})
  rw [equation_eq]
  exact CycleQ2LiteralAmbientCubicRegular.cone_regular

/-- The local coefficient of the cubic cutting out the seed surface is regular on
every open contained in its chart. -/
theorem seed_normalized_regular (i : Fin 4) (V : (threefold (sexticEval seed)).Opens)
    (hi : V ≤ coordinateOpen (sexticEval seed) i) :
    normalized (sexticEval seed) i (quotient (sexticEval seed) (pointEquationH seed))
      (quotient_mem_grade _ _ (pointEquationH_homogeneous seed)) V hi ∈
        nonZeroDivisors Γ(threefold (sexticEval seed), V) :=
  normalized_regular _ _ _ _ seed_cone_regular V hi

end CycleQ2HodgeNormalizedRegular

#print axioms CycleQ2HodgeNormalizedRegular.normalized_regular
#print axioms CycleQ2HodgeNormalizedRegular.seed_normalized_regular
