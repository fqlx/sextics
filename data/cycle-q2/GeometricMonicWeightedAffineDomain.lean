import Proposal.GeometricMonicWeightedAffineEquation
import HodgeComputer.Constructions.HoldoutCover.HypersurfaceDomain

/-!
# Integrality of the universal affine weighted sextic

The coefficient of the pure sixth power of the chart coordinate varies
independently. Giving it value `T` and setting all other tails to zero
specializes the monic equation to `w³ + T`, Eisenstein at `T`.
Monic specialization reflects irreducibility over the full parameter ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2MonicWeightedAffineEquation

open MvPolynomial CycleQ2IncidenceNormalForm
open CycleQ2GeometricHodgeThreefoldCubic (baseValue baseMonomial)

def constantIndex : FullSexticTailIndex :=
  ⟨⟨![6, 0, 0, 0, 0], by decide⟩, by decide⟩

private def coefficientValue (e : FullSexticTailIndex) : Polynomial ℂ :=
  if e = constantIndex then Polynomial.X else 0

private def specializeCoeff : Coeff →+* Polynomial ℂ :=
  eval₂Hom Polynomial.C coefficientValue

def specialize : Coords Coeff →+* Polynomial ℂ :=
  eval₂Hom specializeCoeff (fun _ => 1)

private theorem specialize_baseValue (i : Fin 4) :
    specialize (baseValue 0 i) = 1 := by
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [baseValue]
  · simp [baseValue, specialize]

private theorem specialize_baseMonomial (e : FullSexticTailIndex) :
    specialize (baseMonomial 0 (fullExponentOf e.val.val) (X e)) = coefficientValue e := by
  simp only [baseMonomial, map_mul, map_prod, map_pow, specialize_baseValue, one_pow, Finset.prod_const_one,
    mul_one]
  simp [specialize, specializeCoeff]

theorem universalEquation_specialize :
    universalEquation.map specialize = Polynomial.X ^ 3 + Polynomial.C Polynomial.X := by
  classical
  rw [universalEquation, equation_eq, Polynomial.map_add, Polynomial.map_pow, Polynomial.map_X]
  congr 1
  simp only [tail, Polynomial.map_sum, Polynomial.map_monomial, specialize_baseMonomial]
  rw [Finset.sum_eq_single constantIndex]
  · simp [coefficientValue, constantIndex]
  · intro e _ he
    simp [coefficientValue, he]
  · simp

theorem universalEquation_irreducible : Irreducible universalEquation := by
  apply (monic (fun e : FullSexticTailIndex => (X e : Coeff))).irreducible_of_irreducible_map specialize
  rw [universalEquation_specialize]
  exact HoldoutConstruction.irreducible_power_add_constant (Polynomial.X : Polynomial ℂ)
    (by simp) (by simp) 3 (by decide)

instance universalEquation_domain : IsDomain (AdjoinRoot universalEquation) :=
  AdjoinRoot.isDomain_of_prime universalEquation_irreducible.prime

section
set_option maxRecDepth 8000
set_option maxHeartbeats 700000

/-- A parameter with only the coefficient of the pure sixth power of the
first spatial coordinate nonzero. -/
private def spatialIndex : FullSexticTailIndex :=
  ⟨⟨![0, 6, 0, 0, 0], by decide⟩, by decide⟩

private def spatialCoefficient : Coeff →+* ℂ :=
  eval (fun e => if e = spatialIndex then 1 else 0)

private def spatialBase : Coords Coeff →+* ℂ :=
  eval₂Hom spatialCoefficient (fun _ => 1)

private def spatialPoint : Fin 4 → ℂ := Fin.snoc (fun _ => 1) (-1)

private theorem separate_eval (p : MvPolynomial (Fin 4) Coeff) :
    (separate p).eval₂ spatialBase (-1) = eval spatialPoint (MvPolynomial.map spatialCoefficient p) := by
  suffices h : (Polynomial.eval₂RingHom spatialBase (-1)).comp separate.toRingHom =
      (eval spatialPoint).comp (MvPolynomial.map spatialCoefficient) from DFunLike.congr_fun h p
  apply MvPolynomial.ringHom_ext
  · intro a
    change (separate (C a)).eval₂ spatialBase (-1) = _
    rw [show separate (C a) = Polynomial.C (C a) from separate.commutes a]
    simp [spatialBase]
  · intro i
    change (separate (X i)).eval₂ spatialBase (-1) = _
    refine Fin.lastCases ?_ (fun j => ?_) i
    · rw [separate_last]
      simp [spatialPoint, Fin.snoc]
    · rw [separate_castSucc]
      simp [spatialBase, spatialPoint]

private theorem spatial_chart :
    MvPolynomial.map spatialCoefficient (chart (normalizedFullSextic (fun e => (X e : Coeff)))) =
      (X 3 : MvPolynomial (Fin 4) ℂ)^3 + X 0^6 := by
  classical
  have hchart : (MvPolynomial.map spatialCoefficient (σ := Fin 4)).comp chart.toRingHom =
      chart.toRingHom.comp (MvPolynomial.map spatialCoefficient (σ := Fin 5)) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [chart]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [chart]
  have hf : MvPolynomial.map spatialCoefficient (normalizedFullSextic (fun e => (X e : Coeff))) =
      (X 4 : MvPolynomial (Fin 5) ℂ)^3 + X 1^6 := by
    rw [CycleQ2UniversalSurfaceCoefficientMap.map_sextic, normalizedFullSextic]
    simp only [spatialCoefficient, eval_X]
    rw [Finset.sum_eq_single spatialIndex]
    · have he : fullExponentOf spatialIndex.val.val = Finsupp.single 1 6 := by
        ext i
        fin_cases i <;> simp [spatialIndex]
      simp [he, X_pow_eq_monomial]
    · intro e _ he
      simp [he]
    · simp
  have h4 : Fin.cases (motive := fun _ : Fin 5 => MvPolynomial (Fin 4) ℂ)
      1 X 4 = X 3 := by
    rw [show (4 : Fin 5) = (3 : Fin 4).succ from by decide, Fin.cases_succ]
  have h1 : Fin.cases (motive := fun _ : Fin 5 => MvPolynomial (Fin 4) ℂ)
      1 X 1 = X 0 := by
    rw [show (1 : Fin 5) = (0 : Fin 4).succ from by decide, Fin.cases_succ]
  have h := DFunLike.congr_fun hchart (normalizedFullSextic (fun e => (X e : Coeff)))
  simpa only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom,
    hf, map_add, map_pow, chart, aeval_X, h4, h1] using h

theorem normal_nonzero :
    AdjoinRoot.mk universalEquation
      (separate (pderiv 0 (chart (normalizedFullSextic (fun e => (X e : Coeff)))))) ≠ 0 := by
  have hroot : universalEquation.eval₂ spatialBase (-1) = 0 := by
    rw [show universalEquation = separate (chart (normalizedFullSextic (fun e => (X e : Coeff)))) from
      (separate_chart_equation _).symm, separate_eval, spatial_chart]
    norm_num [spatialPoint, Fin.snoc]
  intro he
  have hp := congrArg (AdjoinRoot.lift spatialBase (-1) hroot) he
  rw [AdjoinRoot.lift_mk, map_zero, separate_eval, ← pderiv_map, spatial_chart] at hp
  have h30 : (3 : Fin 4) ≠ 0 := by decide
  norm_num [pderiv_pow, pderiv_X, Pi.single_apply, spatialPoint, Fin.snoc, h30] at hp

end

end CycleQ2MonicWeightedAffineEquation

end

#print axioms CycleQ2MonicWeightedAffineEquation.universalEquation_irreducible
#print axioms CycleQ2MonicWeightedAffineEquation.universalEquation_domain
#print axioms CycleQ2MonicWeightedAffineEquation.normal_nonzero
