import Proposal.GeometricHodgeTwistAnchorBase
import Proposal.GeometricHodgeEulerChartBinding

/-!
# Homogeneous polynomial representatives of global Laurent forms

The empty pole set forces every exponent of a nonzero term to be
nonnegative. Appending the power of w gives an actual monomial in the
five original cone variables. Its geometric weighted degree is the twist.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeTwistPolynomial

open AlgebraicGeometry CategoryTheory MvPolynomial
open CycleQ2HodgeTwistCech CycleQ2GeometricIncidenceProj
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding
open CycleQ2HodgeTwistRatios (normalized transition)
open CycleQ2HodgeTwistMonomials
open CycleQ2GeometricProjectiveCurve.Twisted (res)
open CycleQ2HodgeTwistAnchor
open CycleQ2GenericSexticGradient (CoeffRing)

def exponent (j : Fin 3) (e : Exp) : Fin 5 →₀ ℕ :=
  Finsupp.equivFunOnFinite.symm (Fin.snoc (fun a => (e a).toNat) j.val)

@[simp] theorem exponent_cast (j : Fin 3) (e : Exp) (a : Vertex) :
    exponent j e a.castSucc = (e a).toNat :=
  Fin.snoc_castSucc (α := fun _ : Fin 5 => ℕ) j.val (fun a => (e a).toNat) a

@[simp] theorem exponent_last (j : Fin 3) (e : Exp) :
    exponent j e (Fin.last 4) = j.val :=
  Fin.snoc_last (α := fun _ : Fin 5 => ℕ) j.val (fun a => (e a).toNat)

theorem weight_exponent (j : Fin 3) (e : Exp) :
    Finsupp.weight geometricWeight (exponent j e) = (∑ a, (e a).toNat) + 2*j.val := by
  rw [Finsupp.weight_eq_sum, Fin.sum_univ_castSucc]
  simp only [exponent_cast, exponent_last, CycleQ2SeedFermatProj.geometricWeight_castSucc,
    show geometricWeight (Fin.last 4) = 2 from rfl, smul_eq_mul, mul_one, Nat.mul_comm]

variable {R : Type} [CommRing R]

private theorem allowed_support {n : ℕ} (p : sections R (n : ℤ) ∅) (j : Fin 3)
    (e : Exp) (he : e ∈ (p.val j).support) : Allowed n ∅ j e := by
  by_contra hn
  exact (Finsupp.mem_support_iff.mp he) (p.property j e hn)

private theorem nonnegative {n : ℕ} {j : Fin 3} {e : Exp} (h : Allowed n ∅ j e) (a : Vertex) :
    0 ≤ e a := by
  by_contra! ha
  exact Finset.notMem_empty a (h.2 a ha)

def representative {n : ℕ} (p : sections R (n : ℤ) ∅) : MvPolynomial (Fin 5) R :=
  ∑ j, (p.val j).sum fun e c => MvPolynomial.monomial (exponent j e) c

theorem representative_homogeneous {n : ℕ} (p : sections R (n : ℤ) ∅) :
    (representative p).IsWeightedHomogeneous geometricWeight n := by
  apply (weightedHomogeneousSubmodule R geometricWeight n).sum_mem
  intro j _
  unfold Finsupp.sum
  apply (weightedHomogeneousSubmodule R geometricWeight n).sum_mem
  intro e he
  apply isWeightedHomogeneous_monomial
  rw [weight_exponent]
  have ha := allowed_support p j e he
  apply Int.ofNat_inj.mp
  push_cast
  simpa only [Int.toNat_of_nonneg (nonnegative ha _)] using ha.1

variable (φ : CoeffRing →+* R) (i : Vertex)

def polynomialMap : MvPolynomial (Fin 5) R →+* Γ(threefold φ, torus φ) :=
  (res (threefold φ).sheaf (torus_le φ i)).comp ((Proj.awayToSection (grade φ) (coord φ i.castSucc)).hom.comp
    ((chartEquiv φ i).symm.toRingHom.comp ((chartMap φ i).toRingHom.comp (dehom (R := R) i).toRingHom)))

theorem polynomialMap_normalized (n : ℕ) (f : MvPolynomial (Fin 5) R) (hf : f.IsWeightedHomogeneous geometricWeight n) :
    polynomialMap φ i f = normalized φ i (quotient φ f) (quotient_mem_grade φ f hf) (torus φ) (torus_le φ i) := by
  change res _ _ ((Proj.awayToSection _ _) ((chartEquiv φ i).symm (chartMap φ i (dehom i f)))) = _
  rw [← chartEquiv_fraction φ i n f hf, AlgEquiv.symm_apply_apply]
  rfl

private def variableValue : Fin 5 → Γ(threefold φ,torus φ) :=
  Fin.snoc (fun a => (transition φ i a (torus φ) (torus_le φ i) (torus_le φ a)).val)
    (weightTwo φ (torus φ) (torus_le φ) i)

private theorem polynomialMap_eval : polynomialMap φ i =
    eval₂Hom (commonCoefficient φ) (variableValue φ i) := by
  apply MvPolynomial.ringHom_ext
  · intro c
    rw [eval₂Hom_C]
    change res _ _ ((Proj.awayToSection _ _) ((chartEquiv φ i).symm
      (chartMap φ i (dehom i (algebraMap R (MvPolynomial (Fin 5) R) c))))) = _
    rw [AlgHom.commutes, AlgHom.commutes, AlgEquiv.commutes]
    exact RingHom.congr_fun (frameCoefficient_eq φ i) c
  · intro a
    rw [eval₂Hom_X', polynomialMap_normalized φ i (geometricWeight a) _ (isWeightedHomogeneous_X R geometricWeight a)]
    induction a using Fin.lastCases with
    | last => rw [variableValue, Fin.snoc_last]; rfl
    | cast a =>
      rw [variableValue, Fin.snoc_castSucc]
      apply congrArg (res (threefold φ).sheaf (torus_le φ i))
      apply congrArg (Proj.awayToSection (grade φ) (coord φ i.castSucc))
      apply HomogeneousLocalization.val_injective
      simp only [HomogeneousLocalization.Away.val_mk, CycleQ2SeedFermatProj.geometricWeight_castSucc]
      rfl

private theorem polynomialMap_monomial {n : ℕ} (j : Fin 3) (e : Exp) (c : R) (ha : Allowed n ∅ j e) :
    polynomialMap φ i (MvPolynomial.monomial (exponent j e) c) =
      commonCoefficient φ c * CycleQ2HodgeTwistMonomials.monomial φ (torus φ) (torus_le φ) i j e := by
  rw [polynomialMap_eval, eval₂Hom_monomial, Finsupp.prod_fintype _ _ (by simp), Fin.prod_univ_castSucc]
  simp only [exponent_cast, exponent_last, variableValue, Fin.snoc_castSucc, Fin.snoc_last,
    CycleQ2HodgeTwistMonomials.monomial]
  congr 2
  change _ = Units.coeHom _ (∏ a, transition φ i a (torus φ) (torus_le φ i) (torus_le φ a) ^ e a)
  rw [map_prod]
  apply Finset.prod_congr rfl
  intro a _
  conv_rhs => rw [← Int.toNat_of_nonneg (nonnegative ha a), zpow_natCast]
  rfl

/-- The normalized native homogeneous section has exactly the prescribed Laurent evaluation. -/
theorem representative_evaluation {n : ℕ} (p : sections R (n : ℤ) ∅) :
    normalized φ i (quotient φ (representative p)) (quotient_mem_grade φ _ (representative_homogeneous p))
      (torus φ) (torus_le φ i) =
      evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) i p.val := by
  rw [← polynomialMap_normalized φ i n _ (representative_homogeneous p), representative, evaluate, map_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [Finsupp.sum, map_sum]
  apply Finset.sum_congr rfl
  intro e he
  exact polynomialMap_monomial φ i j e _ (allowed_support p j e he)

end CycleQ2HodgeTwistPolynomial
end

#print axioms CycleQ2HodgeTwistPolynomial.representative_homogeneous
#print axioms CycleQ2HodgeTwistPolynomial.representative_evaluation
