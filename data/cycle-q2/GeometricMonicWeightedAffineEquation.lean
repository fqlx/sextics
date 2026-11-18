import Proposal.GeometricHodgeThreefoldCubicChart

/-!
# The normalized sextic on the affine chart `x₀ = 1`

Separating the weight-two coordinate from the three affine base coordinates
writes the actual normalized sextic as a monic cubic. Its tail has degree
at most two over any coefficient ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2MonicWeightedAffineEquation

open MvPolynomial CycleQ2IncidenceNormalForm
open CycleQ2GeometricHodgeThreefoldCubic (baseMonomial expand expand_monomial pack pack_X pack_dehom)

abbrev Coeff := MvPolynomial FullSexticTailIndex ℂ
abbrev Coords (R : Type) [CommRing R] := MvPolynomial (Fin 3) R
abbrev Affine (R : Type) [CommRing R] := Polynomial (Coords R)

variable {R : Type} [CommRing R]

/-- Coordinates on the affine chart, in the order `x₁, x₂, x₃, w`. -/
def chart : MvPolynomial (Fin 5) R →ₐ[R] MvPolynomial (Fin 4) R :=
  aeval (Fin.cases 1 X)

/-- The last affine coordinate is the indeterminate over the first three. -/
abbrev separate : MvPolynomial (Fin 4) R ≃ₐ[R] Affine R := pack

theorem separate_castSucc (j : Fin 3) :
    separate (X j.castSucc : MvPolynomial (Fin 4) R) = Polynomial.C (X j) := by
  rw [separate, pack_X, Fin.snoc_castSucc]

theorem separate_last :
    separate (X (Fin.last 3) : MvPolynomial (Fin 4) R) = Polynomial.X := by
  rw [separate, pack_X, Fin.snoc_last]

theorem chart_eq_dehom : chart (R := R) = CycleQ2HodgeEuler.dehom 0 := by
  apply MvPolynomial.algHom_ext
  intro j
  refine Fin.cases ?_ (fun k => ?_) j <;> simp [chart, CycleQ2HodgeEuler.dehom]

theorem separate_chart : (separate (R := R)).toAlgHom.comp chart = expand 0 := by
  apply AlgHom.ext
  intro p
  exact (congrArg separate (DFunLike.congr_fun chart_eq_dehom p)).trans (pack_dehom 0 p)

def equation (c : FullSexticTailIndex → R) : Affine R :=
  expand 0 (normalizedFullSextic c)

theorem separate_chart_equation (c : FullSexticTailIndex → R) :
    separate (chart (normalizedFullSextic c)) = equation c :=
  DFunLike.congr_fun (separate_chart (R := R)) _

def tail (c : FullSexticTailIndex → R) : Affine R :=
  ∑ e : FullSexticTailIndex, Polynomial.monomial (e.val.val 4).val
    (baseMonomial 0 (fullExponentOf e.val.val) (c e))

theorem equation_eq (c : FullSexticTailIndex → R) :
    equation c = Polynomial.X ^ 3 + tail c := by
  simp only [equation, normalizedFullSextic, map_add, map_sum, expand_monomial, tail,
    fullExponentOf_apply, Finsupp.single_eq_same]
  congr 1
  rw [← Polynomial.C_mul_X_pow_eq_monomial]
  have hz (j : Fin 4) : Finsupp.single (4 : Fin 5) (3 : ℕ) j.castSucc = 0 :=
    Finsupp.single_eq_of_ne (Fin.castSucc_ne_last j)
  simp [baseMonomial, hz]

theorem tail_degree (c : FullSexticTailIndex → R) : (tail c).degree < 3 := by
  apply (Polynomial.degree_sum_le _ _).trans_lt
  refine (Finset.sup_lt_iff (show (⊥ : WithBot ℕ) < 3 by decide)).mpr ?_
  intro e _
  exact (Polynomial.degree_monomial_le _ _).trans_lt (WithBot.coe_lt_coe.mpr e.property)

theorem monic (c : FullSexticTailIndex → R) : (equation c).Monic := by
  rw [equation_eq]
  exact Polynomial.monic_X_pow_add (tail_degree c)

theorem natDegree [Nontrivial R] (c : FullSexticTailIndex → R) : (equation c).natDegree = 3 := by
  apply Polynomial.natDegree_eq_of_degree_eq_some
  rw [equation_eq, Polynomial.degree_add_eq_left_of_degree_lt, Polynomial.degree_X_pow]
  rw [Polynomial.degree_X_pow]
  exact (tail_degree c).trans_le (by norm_num)

abbrev universalEquation : Affine Coeff := equation (fun e : FullSexticTailIndex => (X e : Coeff))

end CycleQ2MonicWeightedAffineEquation

end

#print axioms CycleQ2MonicWeightedAffineEquation.separate_chart_equation
#print axioms CycleQ2MonicWeightedAffineEquation.monic
#print axioms CycleQ2MonicWeightedAffineEquation.natDegree
