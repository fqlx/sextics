import Proposal.GeometricHodgeTwistResidueCoefficient
import Proposal.GeometricHodgeTwistChartRestriction
import Proposal.GeometricHodgeTwistPolynomial

/-!
# Polynomial cubic reduction in the common projective torus

The monic cubic is the original hypersurface equation in the affine chart.
Consequently the normalized evaluation of any numerator is the sum of
the three actual base coefficients of its remainder times the three
powers of the normalized weight-two coordinate.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeTwistResidueReduction
open AlgebraicGeometry CategoryTheory MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (vertexCoefficient threefold grade coord chartCoefficient ChartRing)
open CycleQ2GeometricHodgeThreefoldCubic (Stage Base expand cubic cubic_monic cubic_natDegree
  pack_dehom chartEquivAdjoinRoot chartEquivAdjoinRoot_polynomial chartEquivAdjoinRoot_weightTwo)
open CycleQ2HodgeTwistAnchor (torus torus_le nativeUnits commonCoefficient frameCoefficient_eq)
open CycleQ2HodgeTwistCubicFaces (stageEquiv stageEquiv_variable)
open CycleQ2HodgeTwistMonomials (weightTwo)
open CycleQ2GeometricProjectiveCurve.Twisted (res)
open CycleQ2HodgeTwistPolynomial (polynomialMap)
open CycleQ2HodgeTwistResidueCoefficient (Poly remainder)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (hu : IsUnit (φ vertexCoefficient))
abbrev Ring := Γ(threefold φ,torus φ)

private def chartSection : ChartRing φ 0 →+* Ring φ := (res (threefold φ).sheaf (torus_le φ 0)).comp
  (Proj.awayToSection (grade φ) (coord φ (0 : Fin 4).castSucc)).hom

def stageSection : Stage φ 0 hu →+* Ring φ :=
  (chartSection φ).comp (stageEquiv φ 0 hu).symm.toRingHom

def baseSection : Base R →+* Ring φ := (stageSection φ hu).comp (algebraMap (Base R) (Stage φ 0 hu))

def polySection : Polynomial (Base R) →+* Ring φ := (stageSection φ hu).comp (AdjoinRoot.mk _)

theorem baseSection_C (c : R) : baseSection φ hu (C c) = commonCoefficient φ c := by
  have hc : stageEquiv φ 0 hu (chartCoefficient φ 0 c) = algebraMap (Base R) (Stage φ 0 hu) (C c) := by
    rw [show chartCoefficient φ 0 c = algebraMap R (ChartRing φ 0) c from rfl, AlgEquiv.commutes]
    exact IsScalarTower.algebraMap_apply R (Base R) (Stage φ 0 hu) c
  change chartSection φ ((stageEquiv φ 0 hu).symm _) = _
  rw [← hc, AlgEquiv.symm_apply_apply]
  exact RingHom.congr_fun (frameCoefficient_eq φ 0) c

theorem baseSection_X (q : Fin 3) : baseSection φ hu (X q) = (nativeUnits φ 0 q).val := by
  change chartSection φ ((stageEquiv φ 0 hu).symm _) = _
  rw [← stageEquiv_variable φ 0 hu q, AlgEquiv.symm_apply_apply]
  apply congrArg (res (threefold φ).sheaf (torus_le φ 0))
  apply congrArg (Proj.awayToSection (grade φ) (coord φ (0 : Fin 4).castSucc))
  apply HomogeneousLocalization.val_injective
  simp only [CycleQ2HodgeEulerChartBinding.ratio, CycleQ2HodgeEulerChartBinding.fraction,
    CycleQ2SeedFermatProj.geometricWeight_castSucc, HomogeneousLocalization.Away.val_mk, pow_one]
  rfl

theorem polySection_C (p : Base R) : polySection φ hu (Polynomial.C p) = baseSection φ hu p := by
  change stageSection φ hu (AdjoinRoot.mk _ (Polynomial.C p)) = _
  rw [AdjoinRoot.mk_C] <;> rfl

theorem polySection_X : polySection φ hu Polynomial.X = weightTwo φ (torus φ) (torus_le φ) 0 := by
  let e := CycleQ2HodgeEulerChartBinding.ratio φ 0 (Fin.last 4)
  have he : stageEquiv φ 0 hu e = AdjoinRoot.root (cubic φ 0 hu) :=
    (congrArg (chartEquivAdjoinRoot φ 0 hu)
      (CycleQ2HodgeEulerChartBinding.chartEquiv_ratio_succAbove φ 0 (Fin.last 3))).trans
        (chartEquivAdjoinRoot_weightTwo φ 0 hu)
  change chartSection φ ((stageEquiv φ 0 hu).symm (AdjoinRoot.mk _ Polynomial.X)) = _
  rw [AdjoinRoot.mk_X, ← he, AlgEquiv.symm_apply_apply]
  rfl

theorem polySection_expand (p : Poly R) : polySection φ hu (expand 0 p) = polynomialMap φ 0 p := by
  rw [← pack_dehom]
  change chartSection φ ((stageEquiv φ 0 hu).symm (AdjoinRoot.mk _ _)) = _
  rw [← chartEquivAdjoinRoot_polynomial φ 0 hu]
  change chartSection φ ((CycleQ2HodgeEulerChartBinding.chartEquiv φ 0).symm
    ((chartEquivAdjoinRoot φ 0 hu).symm (chartEquivAdjoinRoot φ 0 hu _))) = _
  rw [AlgEquiv.symm_apply_apply] <;> rfl

theorem polySection_remainder (p : Poly R) :
    polySection φ hu (remainder φ hu p) = polynomialMap φ 0 p := by
  have h := congrArg (polySection φ hu) (Polynomial.modByMonic_add_div (expand 0 p) (cubic φ 0 hu))
  have hz : polySection φ hu (cubic φ 0 hu) = 0 := by
    change stageSection _ _ (AdjoinRoot.mk _ _) = 0
    rw [AdjoinRoot.mk_self, map_zero]
  simpa only [remainder, map_add, map_mul, hz, zero_mul, add_zero, polySection_expand] using h

theorem numerator_expansion [Nontrivial R] (p : Poly R) : polynomialMap φ 0 p =
    ∑ j : Fin 3, baseSection φ hu ((remainder φ hu p).coeff j) * weightTwo φ (torus φ) (torus_le φ) 0 ^ j.val := by
  let r := remainder φ hu p
  have hc := cubic_natDegree φ 0 hu
  have hne : cubic φ 0 hu ≠ 1 := by intro h; rw [h, Polynomial.natDegree_one] at hc; omega
  have hr : r.natDegree < 3 := (Polynomial.natDegree_modByMonic_lt (expand 0 p) (cubic_monic φ 0 hu) hne).trans_eq hc
  have he := r.as_sum_range_C_mul_X_pow' hr
  rw [← Fin.sum_univ_eq_sum_range] at he
  rw [← polySection_remainder φ hu p]
  change polySection φ hu r = _
  conv_lhs => rw [he]
  simp only [map_sum, map_mul, map_pow, polySection_C, polySection_X, r]

end CycleQ2HodgeTwistResidueReduction
end
#print axioms CycleQ2HodgeTwistResidueReduction.numerator_expansion
