import Proposal.GeometricHodgeThreefold
import Proposal.GeometricIncidenceProjectiveProper

/-!
# Properness and the Fermat base open of the full weighted sextic

The five-variable graded quotient is finite type over its degree-zero ring,
whose elements all come from the base. The proper structure map of its Proj
is the original algebraic family map. The Fermat point lies in the common
gradient and weight-one chart open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricHodgeThreefold

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2GenericSexticGradient CycleQ2IncidenceNormalForm

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

theorem coefficient_surjective : Function.Surjective (coefficient φ) := by
  rintro ⟨q, hq⟩
  obtain ⟨p,hp,rfl⟩ := hq
  refine ⟨p.coeff 0, Subtype.ext ?_⟩
  exact congrArg (quotient φ) (CycleQ2IncidenceProjectiveProper.polynomialGrade_zero_eq_C p hp).symm

theorem toBase_proper : IsProper (toBase φ) := by
  let : Algebra.FiniteType R (cone φ) :=
    inferInstance
  let : IsScalarTower R (grade φ 0) (cone φ) := ⟨fun a b c => by
    change (a • (b : cone φ)) * c = a • ((b : cone φ) * c)
    exact smul_mul_assoc a (b : cone φ) c⟩
  let : Algebra.FiniteType (grade φ 0) (cone φ) :=
    Algebra.FiniteType.of_restrictScalars_finiteType R (grade φ 0) (cone φ)
  let : IsClosedImmersion (Spec.map (CommRingCat.ofHom (R := R) (S := grade φ 0)
      (coefficient φ))) := IsClosedImmersion.spec_of_surjective _ (coefficient_surjective φ)
  unfold toBase
  infer_instance

theorem seed_vertexCoefficient : seedEvaluation vertexCoefficient = 1 := by
  rw [vertexCoefficient, seedEvaluation, eval_X, fermatCoefficients, fullSexticLeadingIndex_exponent]
  simp [CycleQ2FermatJacobian.fermat, X_pow_eq_monomial, coeff_monomial, Finsupp.single_eq_single_iff]

def goodParameter : CoeffRing := gradientOpen * vertexCoefficient

theorem goodParameter_seed : seedEvaluation goodParameter = 1 := by
  rw [goodParameter, map_mul, gradientOpen_seed, seed_vertexCoefficient, one_mul]

theorem coordinateOpens_cover_of_good (h : IsUnit (φ goodParameter)) :
    (⨆ i : Fin 4, coordinateOpen φ i) = ⊤ := by
  apply coordinateOpens_cover φ
  rw [goodParameter, map_mul, IsUnit.mul_iff] at h
  exact h.2

end CycleQ2GeometricHodgeThreefold
end

#print axioms CycleQ2GeometricHodgeThreefold.toBase_proper
#print axioms CycleQ2GeometricHodgeThreefold.goodParameter_seed
