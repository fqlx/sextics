import Proposal.GeometricHodgeCyclicTwistFrames
import Proposal.GeometricHodgeEulerTangentCover

/-! # The cubic action on the original twist sheaves

For an integral homogeneous degree n ≥ 0, the coefficient in the i-th
frame is scaled by the n-th power of the character of xᵢ. The projective
coordinate ratio transforms by precisely the quotient of its characters.
The local semilinear maps therefore glue to a morphism of module sheaves
with the actual direct image as target.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCyclicTwistMaps
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  CycleQ2GenericSexticGradient CycleQ2GeometricHodgeThreefold CycleQ2HodgeCyclicAction
  CycleQ2LiteralThreefoldOrbitAction CycleQ2HodgeCyclicTwistFrames CycleQ2HodgeThreefoldTwist
  CycleQ2HodgeAtlasLine CycleQ2HodgeTwistRatios CycleQ2GeometricIntrinsicNormal
  CycleQ2GeometricTwistedDifferential
open CycleQ2SeedSectionSheafLocal (moduleRes)

variable (φ : CoeffRing →+* ℂ) (z : ℂ) (hz : z^3=1) (n : ℕ) (c : ℂ)
abbrev L := twist φ (n : ℤ)
abbrev pushed := (Scheme.Modules.pushforward (g φ z hz)).obj (L φ n)
abbrev pre (V : (threefold φ).Opens) := g φ z hz ⁻¹ᵁ V
abbrev weight (i : Fin 4) := c * (char z i.castSucc)^n

private theorem pre_le {V : (threefold φ).Opens} {i : Fin 4} (h : V ≤ U φ i) :
    pre φ z hz V ≤ U φ i := ((g φ z hz).preimage_mono h).trans (coordinateOpen_stable φ z hz i).le

def frameMap (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) :
    Γ(L φ n,V) →ₗ[Γ(threefold φ,V)] Γ(pushed φ z hz n,V) where
  toFun s := (chartFrame φ n i _ (pre_le φ z hz hi)).symm (scalar φ _ (weight z n c i) *
    (g φ z hz).app V (chartFrame φ n i V hi s))
  map_add' s t := by simp only [map_add, mul_add, map_add]
  map_smul' a s := by
    change (chartFrame φ n i _ _).symm (_ * (g φ z hz).app V ((chartFrame φ n i V hi) (a • s))) =
      ((g φ z hz).app V a) • _
    apply (chartFrame φ n i _ (pre_le φ z hz hi)).injective
    rw [LinearEquiv.apply_symm_apply, map_smul, map_smul, LinearEquiv.apply_symm_apply, smul_eq_mul, smul_eq_mul, map_mul]
    ring

theorem frameMap_value (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (s : Γ(L φ n,V)) :
    chartFrame φ n i _ (pre_le φ z hz hi) (frameMap φ z hz n c i V hi s) =
      scalar φ _ (weight z n c i) * (g φ z hz).app V (chartFrame φ n i V hi s) :=
  LinearEquiv.apply_symm_apply _ _

private theorem frame_natural (i : Fin 4) {V W : (threefold φ).Opens} (hi : V ≤ U φ i) (h : W ≤ V) (s : Γ(L φ n,V)) :
    frameMap φ z hz n c i W (h.trans hi) (moduleRes (L φ n) h s) =
      moduleRes (pushed φ z hz n) h (frameMap φ z hz n c i V hi s) := by
  let hpre := (g φ z hz).preimage_mono h
  apply (chartFrame φ n i _ (pre_le φ z hz (h.trans hi))).injective
  change (chartFrame φ n i _ _) (frameMap φ z hz n c i W _ _) =
    coordinate (cocycle φ n) i _ _ (moduleRes (L φ n) hpre _)
  rw [frameMap_value, coordinate_restrict]
  change _ = restrictRing (X := threefold φ) hpre (chartFrame φ n i _ _ (frameMap φ z hz n c i V hi s))
  rw [frameMap_value, map_mul, coefficientOn_restrict]
  apply congrArg (fun b => scalar φ _ (weight z n c i) * b)
  change (g φ z hz).app W (coordinate _ i W _ (moduleRes (L φ n) h s)) = _
  rw [coordinate_restrict]
  exact ConcreteCategory.congr_hom ((g φ z hz).naturality (homOfLE h).op) _

def patch (i : Fin 4) : (L φ n).over (U φ i) ⟶ (pushed φ z hz n).over (U φ i) where
  val.app O := ModuleCat.ofHom (frameMap φ z hz n c i O.unop.left O.unop.hom.le)
  val.naturality {O P} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact frame_natural φ z hz n c i O.unop.hom.le h.unop.left.le

include hz in
private theorem ratio_weight (i j : Fin 4) :
    weight z n c i * (char z j.castSucc * baseScale z i)^n = weight z n c j := by
  have h : char z i.castSucc * (char z j.castSucc * baseScale z i) = char z j.castSucc := by
    rw [baseScale, mul_left_comm, mul_inv_cancel₀ (char_ne_zero z hz _), mul_one]
  rw [weight, weight, mul_assoc, ← mul_pow, h]

include hz in
private theorem frame_agree (i j : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (hj : V ≤ U φ j)
    (s : Γ(L φ n,V)) : frameMap φ z hz n c i V hi s = frameMap φ z hz n c j V hj s := by
  let W := pre φ z hz V
  let ui := pre_le φ z hz hi
  let uj := pre_le φ z hz hj
  have ht := ratio_pull φ z hz i V W hi ui le_rfl j
  rw [Scheme.Hom.appLE_eq_app] at ht
  apply (chartFrame φ n i W ui).injective
  rw [frameMap_value, chartFrame_transition φ n i j W ui uj, frameMap_value,
    chartFrame_transition φ n i j V hi hj]
  simp only [zpow_natCast, Units.val_pow_eq_pow_val, transition, map_mul, map_pow]
  change scalar φ W (weight z n c i) * (((g φ z hz).app V (CycleQ2HodgeTwistRatios.ratio φ i j V hi))^n * _) =
    CycleQ2HodgeTwistRatios.ratio φ i j W ui ^ n * (scalar φ W (weight z n c j) * _)
  rw [ht, mul_pow, ← ratio_weight z hz n c i j]
  simp only [map_mul, map_pow]
  ring

def localSection (i : Fin 4) : LocalLinearHom (threefold φ).sheaf (L φ n) (pushed φ z hz n) (U φ i) :=
  (localLinearHomEquiv _ _ _ _).symm (patch φ z hz n c i)

private theorem agree (i j : Fin 4) :
    restrictLocalLinearHom (threefold φ).sheaf (L φ n) (pushed φ z hz n)
      (homOfLE (show U φ i ⊓ U φ j ≤ U φ i from inf_le_left)).op (localSection φ z hz n c i) =
    restrictLocalLinearHom (threefold φ).sheaf (L φ n) (pushed φ z hz n)
      (homOfLE (show U φ i ⊓ U φ j ≤ U φ j from inf_le_right)).op (localSection φ z hz n c j) := by
  apply localLinearHom_ext
  intro V s
  exact frame_agree φ z hz n c i j V.left (V.hom.le.trans inf_le_left) (V.hom.le.trans inf_le_right) s

variable (hg : IsUnit (φ goodParameter))

def twistMap : L φ n ⟶ pushed φ z hz n :=
  CycleQ2HodgeEulerTangentCover.glue _ _ (U φ) (coordinateOpens_cover_of_good φ hg)
    (localSection φ z hz n c) (agree φ z hz n c)

theorem twistMap_frame (i : Fin 4) (V : (threefold φ).Opens) (hi : V ≤ U φ i) (s : Γ(L φ n,V)) :
    chartFrame φ n i _ (pre_le φ z hz hi) ((twistMap φ z hz n c hg).app V s) =
      scalar φ _ (weight z n c i) * (g φ z hz).app V (chartFrame φ n i V hi s) := by
  rw [twistMap, CycleQ2HodgeEulerTangentCover.glue_apply _ _ _ _ _ _ i V hi s]
  exact frameMap_value φ z hz n c i V hi s

end CycleQ2HodgeCyclicTwistMaps
end
#print axioms CycleQ2HodgeCyclicTwistMaps.twistMap_frame
