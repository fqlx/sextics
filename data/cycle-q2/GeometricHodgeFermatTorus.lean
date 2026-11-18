import Proposal.GeometricHodgeFermatTraceRows

/-!
# Fermat monomials on the actual common projective torus

The original hypersurface equation gives the cubic relation for w/x₀²
as an equality of native sections. Reducing a bounded monomial by this
relation gives its Laurent normal form before applying the derived trace.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeFermatTorus
open AlgebraicGeometry CategoryTheory MvPolynomial
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricIncidenceProj
open CycleQ2HodgeTwistCech CycleQ2HodgeTwistAnchor CycleQ2HodgeTwistMonomials
open CycleQ2HodgeTwistPolynomial (polynomialMap polynomialMap_normalized)
open CycleQ2GenericSexticGradient (seedEvaluation universalF_seed)
open CycleQ2HodgeFermatTraceRows
open CycleQ2GeometricProjectiveCurve.Twisted (res)

abbrev W := torus seedEvaluation
abbrev Ring := Γ(threefold seedEvaluation,W)
abbrev ρ := commonCoefficient seedEvaluation
def x (a : Vertex) : Ringˣ :=
  CycleQ2HodgeTwistRatios.transition seedEvaluation 0 a W (torus_le _ 0) (torus_le _ a)
def z : Ring := weightTwo seedEvaluation W (torus_le _) 0

def powerUnit (e : Exp) : Ringˣ := ∏ a, x a ^ e a

theorem powerUnit_add (e f : Exp) : powerUnit (e+f) = powerUnit e * powerUnit f := by
  simp [powerUnit, Pi.add_apply, zpow_add, Finset.prod_mul_distrib]

private theorem polynomialMap_x (a : Vertex) : polynomialMap seedEvaluation 0 (X a.castSucc) = (x a).val := by
  rw [polynomialMap_normalized _ _ _ _ (isWeightedHomogeneous_X ℂ geometricWeight a.castSucc)]
  apply congrArg (res _ (torus_le seedEvaluation 0))
  apply congrArg (Proj.awayToSection (grade seedEvaluation) _)
  apply HomogeneousLocalization.val_injective
  simp only [HomogeneousLocalization.Away.val_mk, CycleQ2SeedFermatProj.geometricWeight_castSucc]
  rfl

private theorem polynomialMap_z : polynomialMap seedEvaluation 0 (X (Fin.last 4)) = z := by
  rw [polynomialMap_normalized _ _ _ _ (isWeightedHomogeneous_X ℂ geometricWeight (Fin.last 4))]
  rfl

private theorem polynomialMap_scalar (c : ℂ) : polynomialMap seedEvaluation 0 (C c) = ρ c := by
  change res _ _ ((Proj.awayToSection _ _) ((CycleQ2HodgeEulerChartBinding.chartEquiv seedEvaluation 0).symm
      (CycleQ2HodgeEuler.chartMap seedEvaluation 0 (CycleQ2HodgeEuler.dehom 0
        (algebraMap ℂ (MvPolynomial (Fin 5) ℂ) c))))) = _
  rw [AlgHom.commutes, AlgHom.commutes, AlgEquiv.commutes]
  exact RingHom.congr_fun (frameCoefficient_eq seedEvaluation 0) c

theorem z_cube : z^3 = -∑ a, (x a).val^6 := by
  have hf : polynomialMap seedEvaluation 0 (equation seedEvaluation) = 0 := by
    change res _ _ ((Proj.awayToSection _ _) ((CycleQ2HodgeEulerChartBinding.chartEquiv seedEvaluation 0).symm
      (CycleQ2HodgeEuler.chartMap seedEvaluation 0 (CycleQ2HodgeEuler.F seedEvaluation 0)))) = 0
    rw [CycleQ2HodgeEuler.chartMap_F, map_zero, map_zero, map_zero]
  have he : equation seedEvaluation = (∑ a : Vertex, (X a.castSucc)^6) + X (Fin.last 4)^3 := by
    rw [equation, universalF_seed, Fin.sum_univ_four] <;> rfl
  rw [he, map_add, map_sum, map_pow, polynomialMap_z] at hf
  simp only [map_pow, polynomialMap_x] at hf
  linear_combination hf

def evaluation : CycleQ2HodgeTopCech.TopSection ℂ 0 →+ Ring where
  toFun p := evaluate seedEvaluation W (torus_le _) ρ 0 p.val
  map_zero' := by change (∑ j : Fin 3, (0 : Exp →₀ ℂ).sum _) = 0; simp
  map_add' p q := by
    classical
    change (∑ j, (p.val j + q.val j).sum _) = (∑ j, (p.val j).sum _) + ∑ j, (q.val j).sum _
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    exact Finsupp.sum_add_index (by simp) (by simp [add_mul])

theorem evaluation_term (j : Fin 3) (e : Exp) (c : ℂ) (hd) :
    evaluation (term j e c hd) = ρ c * ((powerUnit e).val * z^j.val) := by
  classical
  change (∑ k : Fin 3, (if k = j then Finsupp.single e c else (0 : Exp →₀ ℂ)).sum
    (fun b r => ρ r * CycleQ2HodgeTwistMonomials.monomial seedEvaluation W (torus_le _) 0 k b)) = _
  rw [Finset.sum_eq_single j]
  · rw [if_pos rfl, Finsupp.sum_single_index (by simp)] <;> rfl
  · intro k _ hk
    simp [hk]
  · simp

private theorem powerUnit_plusSix (e : Exp) (a : Vertex) :
    (powerUnit (plusSix e a)).val = (powerUnit e).val * (x a).val ^ 6 := by
  change (powerUnit (e + fun k => if k = a then 6 else 0)).val = _
  rw [powerUnit_add, Units.val_mul]
  congr 1
  change ((∏ k : Vertex, x k ^ (if k = a then (6 : ℤ) else 0) : Ringˣ) : Ring) = _
  rw [Finset.prod_eq_single a]
  · simp
  · intro b _ hb; simp [hb]
  · simp

theorem evaluation_normalForm (d : Fin 5 →₀ ℕ) (hd : Degree d) (hm : power d ≤ 4) (c : ℂ) :
    evaluation (normalForm d hd hm c) = ρ c * ((powerUnit (shift d)).val * z ^ power d) := by
  by_cases hb : power d < 3
  · simp only [normalForm, dif_pos hb, evaluation_term]
  · rw [normalForm, dif_neg hb, map_neg, map_sum]
    simp only [evaluation_term, powerUnit_plusSix]
    have hpow : z^power d = z^(power d-3)*z^3 := by rw [← pow_add]; congr 1; omega
    rw [hpow, z_cube]
    simp only [mul_neg, Finset.mul_sum, neg_inj]
    apply Finset.sum_congr rfl
    intro a _
    ring

def denominator : Ring := (powerUnit (fun _ => -5)).val

theorem denominator_eq : denominator = ∏ a : Vertex, ((x a)^(-5 : ℤ)).val := by
  change Units.coeHom Ring (∏ a : Vertex, (x a)^(-5 : ℤ)) = _
  rw [map_prod] <;> rfl

theorem original_monomial (d : Fin 5 →₀ ℕ) (hd : Degree d) (hm : power d ≤ 4) (c : ℂ) :
    polynomialMap seedEvaluation 0 (MvPolynomial.monomial d c) * z * denominator =
      evaluation (normalForm d hd hm c) := by
  rw [evaluation_normalForm, MvPolynomial.monomial_eq, Finsupp.prod_fintype _ _ (by simp),
    map_mul, polynomialMap_scalar, map_prod, Fin.prod_univ_castSucc]
  simp only [map_pow, polynomialMap_x, polynomialMap_z]
  have he : shift d = (fun a => (d a.castSucc : ℤ)) + fun _ => -5 := by funext a; simp [shift, sub_eq_add_neg]
  have hprod : (powerUnit (fun a => (d a.castSucc : ℤ))).val = ∏ a : Vertex, (x a).val ^ d a.castSucc := by
    change Units.coeHom Ring (∏ a : Vertex, x a ^ (d a.castSucc : ℤ)) = _
    rw [map_prod]
    apply Finset.prod_congr rfl
    intro a _
    rw [zpow_natCast] <;> rfl
  rw [he, powerUnit_add, Units.val_mul, hprod, power, pow_add, pow_one]
  unfold denominator
  ring

end CycleQ2HodgeFermatTorus
end

#print axioms CycleQ2HodgeFermatTorus.z_cube
#print axioms CycleQ2HodgeFermatTorus.original_monomial
