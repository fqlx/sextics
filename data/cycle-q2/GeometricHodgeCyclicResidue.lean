import Proposal.GeometricHodgeCyclicAction
import Proposal.GeometricHodgeEulerContractionRestriction

/-!
# The determinant character on the moving sextic residue

On each coordinate chart the diagonal action scales each affine coordinate.
The residue generator on an invertible-gradient patch is divided by the
corresponding partial derivative. Its character is the product of all four
coordinate factors, including the omitted gradient coordinate. Contraction
with this generator shifts the character of tangent vectors by two.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeCyclicAction

open MvPolynomial Module CycleQ2GeometricIncidenceProj CycleQ2GenericSexticGradient
  CycleQ2HodgeEuler CycleQ2HodgeEulerChartDerivations CycleQ2HodgeEulerContractionCharts
  CycleQ2HodgeEulerContractionRestriction CycleQ2LiteralThreefoldResidueContraction
  CycleQ2LiteralThreefoldOrbitAction
open scoped KaehlerDifferential

variable (φ : CoeffRing →+* ℂ) (z : ℂ) (hz : z^3=1) (i j : Fin 4)

include hz in
theorem chartFactor_ne_zero : chartFactor z i j ≠ 0 :=
  mul_ne_zero (char_ne_zero z hz _) (pow_ne_zero _ (inv_ne_zero (char_ne_zero z hz _)))

include hz in
theorem chartFactor_det : ∏ b : Fin 4, chartFactor z i b = z^2 := by
  have h := Fin.prod_univ_succAbove (factor z i) i.castSucc
  rw [factor_self z hz i, one_mul] at h
  change (∏ b : Fin 4, factor z i (i.castSucc.succAbove b)) = z^2
  rw [← h]
  simp only [factor, Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  have hw : ∑ b : Fin 5, geometricWeight b = 6 := by decide
  have hh : ∏ b : Fin 5, char z b = z^2 := by
    simp only [Fin.prod_univ_five, char]
    change z^2 * z^2 * z * 1 * 1 = z^2
    linear_combination z^2 * hz
  rw [hw, baseScale_six z hz, hh, mul_one]

theorem chartPoly_X (a : Fin 4) : chartPoly z i (X a) = C (chartFactor z i a) * X a :=
  aeval_X _ _

private theorem partial_chartPoly (p : MvPolynomial (Fin 4) ℂ) :
    pderiv j (chartPoly z i p) = C (chartFactor z i j) * chartPoly z i (pderiv j p) := by
  induction p using MvPolynomial.induction_on with
  | C c => rw [show chartPoly z i (C c) = C c from (chartPoly z i).commutes c, pderiv_C, map_zero, mul_zero]
  | add p q h k => simp only [map_add, h, k, mul_add]
  | mul_X p a h =>
    have he : pderiv j (chartPoly z i (X a)) = C (chartFactor z i j) * chartPoly z i (pderiv j (X a)) := by
      rw [chartPoly_X, pderiv_C_mul]
      by_cases ha : a=j
      · subst a
        rw [pderiv_X_self, map_one]
      · rw [pderiv_X_of_ne ha, map_zero, mul_zero, mul_zero]
    simp only [map_mul, pderiv_mul, h, he, map_add]
    ring

theorem chartAction_gradient :
    chartAction φ z hz i (gradientEntry (F φ i) j) =
      algebraMap ℂ (chart φ i) (chartFactor z i j)⁻¹ * gradientEntry (F φ i) j := by
  have h := partial_chartPoly z i j (F φ i)
  rw [chartPoly_F φ z hz i] at h
  have h' : chartPoly z i (pderiv j (F φ i)) = C (chartFactor z i j)⁻¹ * pderiv j (F φ i) := by
    conv_rhs => rw [h]
    rw [← mul_assoc, ← map_mul, inv_mul_cancel₀ (chartFactor_ne_zero z hz i j), map_one, one_mul]
  exact congrArg (chartMap φ i) h' |>.trans ((chartMap φ i).map_mul _ _)

abbrev gradientPatch := Patch (F φ i) j

private theorem gradientUnit :
    IsUnit (((patchMap (F φ i) j).comp (chartAction φ z hz i)) (gradientEntry (F φ i) j)) := by
  rw [AlgHom.comp_apply, chartAction_gradient, map_mul]
  exact ((isUnit_iff_ne_zero.mpr (inv_ne_zero (chartFactor_ne_zero z hz i j))).map
    ((patchMap (F φ i) j).toRingHom.comp (algebraMap ℂ (chart φ i)))).mul
    (IsLocalization.Away.algebraMap_isUnit (S := gradientPatch φ i j) _)

def patchAction : gradientPatch φ i j →ₐ[ℂ] gradientPatch φ i j :=
  fromPatch (F φ i) j ((patchMap (F φ i) j).comp (chartAction φ z hz i)) (gradientUnit φ z hz i j)

theorem patchAction_base (x : chart φ i) :
    patchAction φ z hz i j (patchMap (F φ i) j x) =
      patchMap (F φ i) j (chartAction φ z hz i x) :=
  AlgHom.congr_fun (fromPatch_comp (F φ i) j _ (gradientUnit φ z hz i j)) x

private theorem patchAction_gradient :
    patchAction φ z hz i j (patchMap (F φ i) j (gradientEntry (F φ i) j)) =
      algebraMap ℂ (gradientPatch φ i j) (chartFactor z i j)⁻¹ *
        patchMap (F φ i) j (gradientEntry (F φ i) j) := by
  rw [patchAction_base, chartAction_gradient, map_mul, AlgHom.commutes]

private theorem patchAction_dx (a : Fin 4) :
    pullOne (patchAction φ z hz i j) (dx (F φ i) (patchMap (F φ i) j) a) =
      algebraMap ℂ (gradientPatch φ i j) (chartFactor z i a) • dx (F φ i) (patchMap (F φ i) j) a := by
  unfold dx
  rw [pullOne_D, patchAction_base]
  change KaehlerDifferential.D ℂ _ (patchMap _ j (chartMap φ i (chartPoly z i (X a)))) = _
  rw [chartPoly_X, map_mul, map_mul, show chartMap φ i (C (chartFactor z i a)) =
    algebraMap ℂ (chart φ i) (chartFactor z i a) from (chartMap φ i).commutes _, AlgHom.commutes,
    Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]
  rfl

set_option maxHeartbeats 1500000 in
theorem patchAction_residue :
    pull (patchAction φ z hz i j) 3 (projectiveResidue (F φ i) i j) =
      algebraMap ℂ (gradientPatch φ i j) (z^2) • projectiveResidue (F φ i) i j := by
  let P := gradientPatch φ i j
  let d : Fin 4 → P := fun a => algebraMap ℂ P (chartFactor z i a)
  let g := patchMap (F φ i) j (gradientEntry (F φ i) j)
  let E := exteriorPower.ιMulti P 3 (basis (F φ i) j)
  have he : pull (patchAction φ z hz i j) 3 E = (∏ k : Fin 3, d (j.succAbove k)) • E := by
    rw [show E = exteriorPower.ιMulti P 3 (basis (F φ i) j) from rfl, pull_wedge]
    have hb (k : Fin 3) : pullOne (patchAction φ z hz i j) (basis (F φ i) j k) =
        d (j.succAbove k) • basis (F φ i) j k := by
      rw [basis_apply, patchAction_dx]
    simp_rw [hb]
    exact (exteriorPower.ιMulti P 3).map_smul_univ _ _
  have h := congrArg (pull (patchAction φ z hz i j) 3) (partial_smul_projectiveResidue (F φ i) i j)
  change pull _ 3 (g • projectiveResidue _ i j) = pull _ 3 ((-1:P)^(i.val+j.val) • E) at h
  rw [map_smulₛₗ, map_smulₛₗ, he] at h
  have hg : patchAction φ z hz i j g = algebraMap ℂ P (chartFactor z i j)⁻¹ * g :=
    patchAction_gradient φ z hz i j
  change patchAction φ z hz i j g • _ = patchAction φ z hz i j ((-1:P)^(i.val+j.val)) • _ at h
  rw [hg, map_pow, map_neg, map_one] at h
  have hden : d j * algebraMap ℂ P (chartFactor z i j)⁻¹ = 1 := by
    dsimp only [d]
    rw [← map_mul, mul_inv_cancel₀ (chartFactor_ne_zero z hz i j), map_one]
  have hdet : d j * ∏ k : Fin 3, d (j.succAbove k) = algebraMap ℂ P (z^2) := by
    rw [← Fin.prod_univ_succAbove d j, ← chartFactor_det z hz i]
    exact (map_prod (algebraMap ℂ P) _ _).symm
  have e := congrArg (fun x : ⋀[P]^3 Ω[P⁄ℂ] => d j • x) h
  change d j • ((algebraMap ℂ P (chartFactor z i j)⁻¹ * g) • _) =
    d j • ((-1:P)^(i.val+j.val) • ((∏ k : Fin 3, d (j.succAbove k)) • E)) at e
  simp only [← mul_smul, ← mul_assoc, hden, one_mul] at e
  apply (IsUnit.smul_left_cancel (IsLocalization.Away.algebraMap_isUnit (S := P) (gradientEntry (F φ i) j))).mp
  change g • _ = g • (algebraMap ℂ P (z^2) • projectiveResidue _ i j)
  rw [smul_comm g, partial_smul_projectiveResidue, ← mul_smul]
  refine e.trans ?_
  apply congrArg (fun c : P => c • E)
  rw [← hdet]
  ring

include hz in
private theorem chartFactor_cube (a : Fin 4) : chartFactor z i a ^ 3 = 1 := by
  rw [chartFactor, factor, mul_pow, char_cube z hz, one_mul, ← pow_mul, Nat.mul_comm, pow_mul,
    baseScale_cube z hz i, one_pow]

include hz in
private theorem chartPoly_cube : (chartPoly z i).comp ((chartPoly z i).comp (chartPoly z i)) = AlgHom.id ℂ _ := by
  apply MvPolynomial.algHom_ext
  intro a
  simp only [AlgHom.comp_apply, chartPoly_X, map_mul, show ∀ c : ℂ, chartPoly z i (C c) = C c from
    fun c => (chartPoly z i).commutes c, AlgHom.id_apply]
  have h := congrArg (fun x : ℂ => (C x : MvPolynomial (Fin 4) ℂ)) (chartFactor_cube z hz i a)
  rw [map_pow, map_one] at h
  linear_combination X a * h

private theorem chartAction_cube (x : chart φ i) :
    chartAction φ z hz i (chartAction φ z hz i (chartAction φ z hz i x)) = x := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (chartMap φ i) (AlgHom.congr_fun (chartPoly_cube z hz i) p)

theorem patchAction_cube (x : gradientPatch φ i j) :
    patchAction φ z hz i j (patchAction φ z hz i j (patchAction φ z hz i j x)) = x := by
  let g := patchAction φ z hz i j
  have he : g.toRingHom.comp (g.toRingHom.comp g.toRingHom) = RingHom.id _ := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (gradientEntry (F φ i) j))
    apply RingHom.ext
    intro a
    change patchAction φ z hz i j (patchAction φ z hz i j (patchAction φ z hz i j
      (patchMap _ j a))) = patchMap _ j a
    rw [patchAction_base, patchAction_base, patchAction_base, chartAction_cube]
  exact RingHom.congr_fun he x

def patchEquiv : gradientPatch φ i j ≃ₐ[ℂ] gradientPatch φ i j where
  __ := patchAction φ z hz i j
  invFun x := patchAction φ z hz i j (patchAction φ z hz i j x)
  left_inv := patchAction_cube φ z hz i j
  right_inv := patchAction_cube φ z hz i j

def conjugate {A : Type} [CommRing A] [Algebra ℂ A] (e : A ≃ₐ[ℂ] A) (v : Derivation ℂ A A) :
    Derivation ℂ A A where
  toLinearMap := e.toLinearMap.comp (v.toLinearMap.comp e.symm.toLinearMap)
  map_one_eq_zero' := by change e (v (e.symm 1)) = 0; rw [map_one, Derivation.map_one_eq_zero, map_zero]
  leibniz' x y := by
    change e (v (e.symm (x * y))) = x * e (v (e.symm y)) + y * e (v (e.symm x))
    rw [map_mul, Derivation.leibniz, map_add, smul_eq_mul, smul_eq_mul, map_mul, map_mul,
      AlgEquiv.apply_symm_apply, AlgEquiv.apply_symm_apply]

theorem conjugate_apply {A : Type} [CommRing A] [Algebra ℂ A] (e : A ≃ₐ[ℂ] A)
    (v : Derivation ℂ A A) (x : A) : conjugate e v (e x) = e (v x) := by
  change e (v (e.symm (e x))) = e (v x)
  rw [e.symm_apply_apply]

theorem patchEquiv_apply (x : gradientPatch φ i j) :
    patchEquiv φ z hz i j x = patchAction φ z hz i j x := rfl

set_option maxHeartbeats 1500000 in
theorem patchAction_contraction (v : Derivation ℂ (gradientPatch φ i j) (gradientPatch φ i j)) :
    pull (patchAction φ z hz i j) 2 (familyContraction φ i j v) =
      algebraMap ℂ (gradientPatch φ i j) (z^2) •
        familyContraction φ i j (conjugate (patchEquiv φ z hz i j) v) := by
  let u := conjugate (patchEquiv φ z hz i j) v
  have hu (x : gradientPatch φ i j) : u (patchAction φ z hz i j x) = patchAction φ z hz i j (v x) := by
    simpa only [patchEquiv_apply] using conjugate_apply (patchEquiv φ z hz i j) v x
  change pull (patchAction φ z hz i j) 2 (familyContraction φ i j v) = _ • familyContraction φ i j u
  rw [familyContraction_apply, familyContraction_apply,
    pull_contraction (patchAction φ z hz i j) v u hu (projectiveResidue (F φ i) i j),
    patchAction_residue, map_smul]

set_option maxHeartbeats 1500000 in
theorem character_one_contraction_fixed (v : Derivation ℂ (gradientPatch φ i j) (gradientPatch φ i j))
    (hv : conjugate (patchEquiv φ z hz i j) v = algebraMap ℂ (gradientPatch φ i j) z • v) :
    pull (patchAction φ z hz i j) 2 (familyContraction φ i j v) = familyContraction φ i j v := by
  rw [patchAction_contraction, hv, map_smul, ← mul_smul, ← map_mul, ← pow_succ, hz, map_one, one_smul]

end CycleQ2HodgeCyclicAction
end
#print axioms CycleQ2HodgeCyclicAction.patchAction_residue

#print axioms CycleQ2HodgeCyclicAction.character_one_contraction_fixed
