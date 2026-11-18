import Proposal.GeometricHodgeThreefold
import Proposal.GeometricHodgeEuler
import Proposal.GeometricMonicWeightedPrimitiveIdentity
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# The regular coefficient of the cubic-pole cone vertex

The normal derivative alone is inverted in the logarithmic coefficient. Thus the
coefficient can be evaluated directly at points of G=0. On z₀=1 the coordinate
z₁ gives precisely the normal used in the weighted primitive equation.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2WeightedConeVertex

open MvPolynomial

abbrev Poly (ι k : Type*) [CommRing k] := MvPolynomial ι k

variable {ι k : Type} [Field k] [CharZero k]
variable (i : ι) (F B : Poly ι k)

def grad := pderiv i F

def jetNumerator : Poly ι k :=
  let n := grad i F
  let n₁ := pderiv i n
  let n₂ := pderiv i n₁
  pderiv i (pderiv i B) * n^2 -
    (3 * pderiv i B * n₁ + B * n₂) * n + 3 * B * n₁^2

abbrev GradientRing := Localization.Away (grad i F)

/-- This element is regular where the chosen normal partial is a unit, including
points of the hypersurface. -/
def residueSection : GradientRing i F :=
  algebraMap (Poly ι k) _ (C ((2 : k)⁻¹) * jetNumerator i F B) *
    (IsLocalization.Away.invSelf (S := GradientRing i F) (grad i F))^5

variable {L : Type*} [Field L] [CharZero L] (v : Poly ι k →+* L)

def evalSection (hg : v (grad i F) ≠ 0) : GradientRing i F →+* L :=
  IsLocalization.Away.lift (grad i F) (isUnit_iff_ne_zero.mpr hg)

theorem evalSection_residue (hg : v (grad i F) ≠ 0) :
    evalSection i F v hg (residueSection i F B) =
      SplitHigherResidue.normalSourceTwo (v B) (v (pderiv i B)) (v (pderiv i (pderiv i B)))
        (v (grad i F)) (v (pderiv i (grad i F))) (v (pderiv i (pderiv i (grad i F)))) /
      v (grad i F) := by
  let g := grad i F
  let e := evalSection i F v hg
  have he (a : Poly ι k) : e (algebraMap _ _ a) = v a :=
    IsLocalization.Away.lift_eq _ _ _
  have hx : e (IsLocalization.Away.invSelf (S := GradientRing i F) g) = (v g)⁻¹ := by
    have h := congrArg e (IsLocalization.Away.mul_invSelf (S := GradientRing i F) g)
    rw [map_mul,he,map_one] at h
    exact (mul_left_cancel₀ hg) (h.trans (mul_inv_cancel₀ hg).symm)
  have htwo : v (C ((2 : k)⁻¹)) = (2:L)⁻¹ := by
    change (v.comp C) ((2 : k)⁻¹) = _
    rw [map_inv₀, map_ofNat]
  change e (algebraMap (Poly ι k) (GradientRing i F) (C ((2 : k)⁻¹) * jetNumerator i F B) *
    (IsLocalization.Away.invSelf (S := GradientRing i F) g)^5) = _
  rw [map_mul, map_pow, he, hx, map_mul, htwo]
  simp only [jetNumerator, map_sub, map_mul, map_add, map_pow, map_ofNat,
    SplitHigherResidue.normalSourceTwo, g]
  field_simp [hg] <;> ring

open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeEuler (dehom)
open CycleQ2MonicWeightedPrimitiveIdentity (b density normal)

def coneNumerator (k : Type*) [CommRing k] : Poly (Fin 5) k :=
  X ((0 : Fin 4).castSucc) ^ 2 * X ((0 : Fin 4).succ) ^ 2 *
    X ((1 : Fin 4).succ) ^ 2 * X ((2 : Fin 4).succ) ^ 2 * X ((3 : Fin 4).succ) ^ 2

theorem eval_coneNumerator {A S : Type*} [CommRing A] [CommRing S]
    (v : Poly (Fin 5) A →+* S) :
    v (coneNumerator A) = (v (X 0) * v (X 1) * v (X 2) * v (X 3) * v (X 4))^2 := by
  change v (X 0^2 * X 1^2 * X 2^2 * X 3^2 * X 4^2) = _
  simp only [map_mul,map_pow]
  ring

theorem chartNumerator : dehom (0 : Fin 4) (coneNumerator k) = (b : Poly (Fin 4) k) := by
  have hv (j : Fin 4) : dehom (R := k) 0 (X j.succ) = X j :=
    CycleQ2HodgeEuler.dehom_X_succAbove 0 j
  simp only [coneNumerator, b, map_mul, map_pow, hv, CycleQ2HodgeEuler.dehom_X_self,
    one_pow, one_mul]

private theorem chartPartial (p : Poly (Fin 5) k) :
    dehom 0 (pderiv (1 : Fin 5) p) = pderiv (0 : Fin 4) (dehom 0 p) :=
  (CycleQ2HodgeEuler.pderiv_dehom 0 0 p).symm

/-- Evaluation of the regular cone coefficient on the z₀=1 chart gives the
actual weighted rational residue density at every point with nonzero normal
derivative. -/
theorem chart_density (φ : CoeffRing →+* k) (v₀ : Poly (Fin 4) k →+* L)
    (hg : (v₀.comp (dehom 0).toRingHom) (grad 1 (equation φ)) ≠ 0) :
    evalSection 1 (equation φ) (v₀.comp (dehom 0).toRingHom) hg
        (residueSection 1 (equation φ) (coneNumerator k)) =
      density v₀ (CycleQ2HodgeEuler.F φ 0) := by
  rw [evalSection_residue]
  simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, grad,
    chartPartial, chartNumerator, density, normal, CycleQ2HodgeEuler.F,
    CycleQ2GeometricHodgeThreefold.equation]

end CycleQ2WeightedConeVertex
end

#print axioms CycleQ2WeightedConeVertex.evalSection_residue
#print axioms CycleQ2WeightedConeVertex.chart_density
