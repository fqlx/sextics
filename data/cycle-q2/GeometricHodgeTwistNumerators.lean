import Proposal.GeometricHodgeTwistRatios

/-!
# Original cone numerators in a weight-one projective chart

Dividing by the fixed n-th power of the chart coordinate is additive on
the degree-n piece of the original homogeneous cone. A regular chart
coordinate makes this map injective.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
namespace CycleQ2HodgeTwistNumerators

open AlgebraicGeometry CategoryTheory HomogeneousLocalization
open CycleQ2GeometricHodgeThreefold
open CycleQ2GenericSexticGradient (CoeffRing)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Fin 4) (n : ℕ)
abbrev Local := Localization.Away (coord φ i.castSucc)

def fraction (a : grade φ n) : ChartRing φ i :=
  Away.mk (grade φ) (weightOne_mem_grade φ i) n a.val (by simpa using a.property)

private theorem spec (a : grade φ n) :
    (fraction φ i n a).val * algebraMap (cone φ) (Local φ i) (coord φ i.castSucc ^ n) =
      algebraMap (cone φ) (Local φ i) a.val := by
  rw [fraction, Away.val_mk, Localization.mk_eq_mk']
  exact IsLocalization.mk'_spec (M := Submonoid.powers (coord φ i.castSucc)) (Local φ i) a.val
    ⟨coord φ i.castSucc ^ n, n, rfl⟩

private theorem den_unit : IsUnit (algebraMap (cone φ) (Local φ i) (coord φ i.castSucc ^ n)) := by
  rw [map_pow]
  exact (IsLocalization.Away.algebraMap_isUnit (coord φ i.castSucc)).pow n

def fractionMap : grade φ n →+ ChartRing φ i where
  toFun := fraction φ i n
  map_zero' := by
    apply HomogeneousLocalization.val_injective
    apply (den_unit φ i n).mul_left_inj.mp
    rw [spec, HomogeneousLocalization.val_zero, zero_mul]
    exact map_zero _
  map_add' a b := by
    apply HomogeneousLocalization.val_injective
    apply (den_unit φ i n).mul_left_inj.mp
    rw [spec, HomogeneousLocalization.val_add, add_mul, spec, spec]
    exact map_add _ _ _

theorem fractionMap_injective (hr : IsRegular (coord φ i.castSucc)) :
    Function.Injective (fractionMap φ i n) := by
  intro a b ha
  apply Subtype.ext
  apply IsLocalization.injective (Local φ i) (Submonoid.powers_le.mpr hr.mem_nonZeroDivisors)
  rw [← spec φ i n a, ← spec φ i n b]
  exact congrArg (fun z : ChartRing φ i => z.val * algebraMap (cone φ) (Local φ i) (coord φ i.castSucc ^ n)) ha

def normalizedMap (V : (threefold φ).Opens) (hi : V ≤ coordinateOpen φ i) :
    grade φ n →+ Γ(threefold φ,V) :=
  (CycleQ2GeometricProjectiveCurve.Twisted.res (threefold φ).sheaf hi).toAddMonoidHom.comp
    ((Proj.awayToSection (grade φ) (coord φ i.castSucc)).hom.toAddMonoidHom.comp (fractionMap φ i n))

@[simp] theorem normalizedMap_apply (V : (threefold φ).Opens) (hi : V ≤ coordinateOpen φ i) (a : grade φ n) :
    normalizedMap φ i n V hi a = CycleQ2HodgeTwistRatios.normalized φ i a.val a.property V hi := rfl

theorem normalizedMap_injective (hr : IsRegular (coord φ i.castSucc)) :
    Function.Injective (normalizedMap φ i n (coordinateOpen φ i) le_rfl) := by
  intro a b h
  change CycleQ2GeometricProjectiveCurve.Twisted.res _ le_rfl ((Proj.awayToSection _ _) (fractionMap φ i n a)) =
    CycleQ2GeometricProjectiveCurve.Twisted.res _ le_rfl ((Proj.awayToSection _ _) (fractionMap φ i n b)) at h
  rw [CycleQ2GeometricProjectiveCurve.Twisted.res_self, CycleQ2GeometricProjectiveCurve.Twisted.res_self] at h
  apply fractionMap_injective φ i n hr
  exact (Proj.basicOpenIsoAway (grade φ) (coord φ i.castSucc) (weightOne_mem_grade φ i)
    (by decide)).commRingCatIsoToRingEquiv.injective h

end CycleQ2HodgeTwistNumerators
end

#print axioms CycleQ2HodgeTwistNumerators.normalizedMap_injective
