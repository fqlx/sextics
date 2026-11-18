import Proposal.GeometricLiteralOrbitCurveTwistPullback
import Proposal.GeometricSurfaceResidueFunctoriality

/-!
# Coordinate frames of O_C(7) on the translated surface opens

On the preimage of any of the three surface patches the corresponding
homogeneous coordinate trivializes the curve twist. Each frame is glued
from the two original quartic charts. Their change on every overlap
is the pulled seventh power of the actual surface coordinate ratio.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralOrbitCurveTwistFrames

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  CycleQ2GeometricProjectiveCurve CycleQ2SeedProjectiveImageCocycle
  CycleQ2LiteralMovingPoleComponents CycleQ2LiteralOrbitCurveTwistPullback
  CycleQ2LiteralCurvePositiveTwist CycleQ2GeometricCanonicalGluing CycleQ2GeometricModuleLocalIso

private abbrev C := projectiveCurve 57 1
private abbrev N := curveTwistModule 7
private abbrev U := firstProjectivePatch 57 1
private abbrev V := secondProjectivePatch 57 1
private abbrev Q := overlapProjectivePatch 57 1
private abbrev t := projectiveTransitionUnit 57 1
private abbrev hQ := overlapProjectivePatch_eq 57 1
private abbrev j := componentImmersion

variable (z : ℂ) (hz : z^3 = 1)

def pulledUnit (i k : Fin 3) (A : C.Opens) (hi : A ≤ j z hz ⁻¹ᵁ Patch i)
    (hk : A ≤ j z hz ⁻¹ᵁ Patch k) : Γ(C,A)ˣ :=
  Units.map ((j z hz).appLE (Patch i ⊓ Patch k) A (le_inf hi hk)).hom.toMonoidHom
    (transitionUnit i k _ inf_le_left inf_le_right)

theorem pulledUnit_on (i k : Fin 3) (P : Surface.Opens) (A : C.Opens)
    (hi : P ≤ Patch i) (hk : P ≤ Patch k) (ha : A ≤ j z hz ⁻¹ᵁ P) :
    Units.map ((j z hz).appLE P A ha).hom.toMonoidHom (transitionUnit i k P hi hk) =
      pulledUnit z hz i k A (ha.trans ((j z hz).preimage_mono hi)) (ha.trans ((j z hz).preimage_mono hk)) := by
  let h := le_inf hi hk
  rw [← transitionUnit_restrict i k (Patch i ⊓ Patch k) P h inf_le_left inf_le_right]
  apply Units.ext
  exact ConcreteCategory.congr_hom ((j z hz).map_appLE ha (homOfLE h).op) _

theorem pulledUnit_restrict (i k : Fin 3) (A B : C.Opens) (h : B ≤ A)
    (hi : A ≤ j z hz ⁻¹ᵁ Patch i) (hk : A ≤ j z hz ⁻¹ᵁ Patch k) :
    Units.map (Twisted.res C.sheaf h).toMonoidHom (pulledUnit z hz i k A hi hk) =
      pulledUnit z hz i k B (h.trans hi) (h.trans hk) := by
  apply Units.ext
  exact ConcreteCategory.congr_hom ((j z hz).appLE_map (le_inf hi hk :
    A ≤ j z hz ⁻¹ᵁ (Patch i ⊓ Patch k)) (homOfLE h).op) _

theorem pulledUnit_cocycle (i k l : Fin 3) (A : C.Opens)
    (hi : A ≤ j z hz ⁻¹ᵁ Patch i) (hk : A ≤ j z hz ⁻¹ᵁ Patch k) (hl : A ≤ j z hz ⁻¹ᵁ Patch l) :
    pulledUnit z hz k l A hk hl * pulledUnit z hz i k A hi hk = pulledUnit z hz i l A hi hl := by
  let P := Patch i ⊓ (Patch k ⊓ Patch l)
  have ha : A ≤ j z hz ⁻¹ᵁ P := le_inf hi (le_inf hk hl)
  have h₁ : P ≤ Patch i := inf_le_left
  have h₂ : P ≤ Patch k := inf_le_right.trans inf_le_left
  have h₃ : P ≤ Patch l := inf_le_right.trans inf_le_right
  rw [← pulledUnit_on z hz k l P A h₂ h₃ ha, ← pulledUnit_on z hz i k P A h₁ h₂ ha,
    ← pulledUnit_on z hz i l P A h₁ h₃ ha, ← map_mul, transitionUnit_cocycle]

private def character (A : C.Opens) : Γ(C,A)ˣ :=
  Units.map (curveScalar A).toMonoidHom (Units.mk0 z (by rintro rfl; norm_num at hz))

private theorem character_seventh (A : C.Opens) : character z hz A ^ 7 = character z hz A := by
  apply Units.ext
  change (curveScalar A z)^7 = curveScalar A z
  rw [← map_pow]
  apply congrArg (curveScalar A)
  calc
    z^7 = (z^3)^2*z := by ring
    _ = z := by rw [hz, one_pow, one_mul]

private abbrev quartic : Bool → C.Opens | false => U | true => V
private abbrev idx : Bool → Fin 3 | false => 0 | true => 1

private theorem quartic_le (b : Bool) : quartic b ≤ j z hz ⁻¹ᵁ Patch (idx b) := by
  rw [component_preimage_patch]
  cases b
  · exact CycleQ2GeometricProjectiveAffine.firstProjectivePatch_le_firstCoordinate 57 1
  · exact CycleQ2GeometricProjectiveAffine.secondProjectivePatch_le_secondCoordinate 57 1

private def gauge (b : Bool) (A : C.Opens) : Γ(C,A)ˣ :=
  if b then (character z hz A)⁻¹ else 1

private def factor (b : Bool) (i : Fin 3) (A : C.Opens) (hi : A ≤ j z hz ⁻¹ᵁ Patch i)
    (hq : A ≤ quartic b) : Γ(C,A)ˣ :=
  pulledUnit z hz (idx b) i A (hq.trans (quartic_le z hz b)) hi ^ 7 * gauge z hz b A

private theorem factor_restrict (b : Bool) (i : Fin 3) (A B : C.Opens) (h : B ≤ A)
    (hi : A ≤ j z hz ⁻¹ᵁ Patch i) (hq : A ≤ quartic b) :
    Units.map (Twisted.res C.sheaf h).toMonoidHom (factor z hz b i A hi hq) =
      factor z hz b i B (h.trans hi) (h.trans hq) := by
  unfold factor
  rw [map_mul, map_pow, pulledUnit_restrict]
  congr 1
  cases b
  · exact map_one _
  · change Units.map _ ((character z hz A)⁻¹) = (character z hz B)⁻¹
    rw [map_inv]
    apply congrArg Inv.inv
    apply Units.ext
    exact CycleQ2GeometricTwistedDifferential.coefficientOn_restrict _ _ h z

private def raw : (b : Bool) → LocalFrame C.sheaf N (quartic b)
  | false => twistedFirstFrame C.sheaf U V Q hQ (t^7)
  | true => twistedSecondFrame C.sheaf U V Q hQ (t^7)

private abbrev parts (i : Fin 3) (b : Bool) := (j z hz ⁻¹ᵁ Patch i) ⊓ quartic b

private def localFrame (i : Fin 3) (b : Bool) : LocalFrame C.sheaf N (parts z hz i b) where
  app A h := ((raw b).app A (h.trans inf_le_right)).trans
    (Units.mulLeftLinearEquiv (Γ(C,A)) (Γ(C,A)) (factor z hz b i A (h.trans inf_le_left) (h.trans inf_le_right)))
  naturality {A B} h hA s := by
    let u := factor z hz b i A (hA.trans inf_le_left) (hA.trans inf_le_right)
    change Twisted.res C.sheaf h ((u : Γ(C,A)) * (show Γ(C,A) from (raw b).app A (hA.trans inf_le_right) s)) =
      (factor z hz b i B (h.trans (hA.trans inf_le_left)) (h.trans (hA.trans inf_le_right)) : Γ(C,B)) *
        (show Γ(C,B) from (raw b).app B (h.trans (hA.trans inf_le_right)) (N.val.map (homOfLE h).op s))
    rw [map_mul]
    exact congrArg₂ (· * ·) (congrArg Units.val (factor_restrict z hz b i A B h (hA.trans inf_le_left) (hA.trans inf_le_right)))
      ((raw b).naturality h (hA.trans inf_le_right) s)

private theorem cancel_character {G : Type*} [CommGroup G] (u t χ : G) :
    u * t = (u * (χ * t)) * χ⁻¹ := by
  rw [mul_comm χ t, ← mul_assoc, mul_inv_cancel_right]

set_option maxHeartbeats 2000000 in
private theorem factor_cross (i : Fin 3) (A : C.Opens) (hi : A ≤ j z hz ⁻¹ᵁ Patch i)
    (hU : A ≤ U) (hV : A ≤ V) :
    factor z hz false i A hi hU * (show Γ(C,A)ˣ from Units.map (Twisted.res C.sheaf ((le_inf hU hV).trans hQ.ge)).toMonoidHom (t^7)) =
      factor z hz true i A hi hV := by
  let hA := (le_inf hU hV).trans hQ.ge
  let h₀ := hU.trans (quartic_le z hz false)
  let h₁ := hV.trans (quartic_le z hz true)
  let tA : Γ(C,A)ˣ := Units.map (Twisted.res C.sheaf hA).toMonoidHom t
  have hr : pulledUnit z hz 1 0 A h₁ h₀ = character z hz A * tA := by
    apply Units.ext
    exact component_ratio z hz (Patch 1 ⊓ Patch 0) inf_le_right inf_le_left A hA (le_inf h₁ h₀)
  change (pulledUnit z hz 0 i A h₀ hi ^ 7 * 1) * _ = pulledUnit z hz 1 i A h₁ hi ^ 7 * (character z hz A)⁻¹
  rw [map_pow, mul_one, ← pulledUnit_cocycle z hz 1 0 i A h₁ h₀ hi, hr, mul_pow, mul_pow,
    character_seventh]
  change _ * tA^7 = (_ * (character z hz A * tA^7)) * (character z hz A)⁻¹
  exact cancel_character (pulledUnit z hz 0 i A h₀ hi ^ 7) (tA^7) (character z hz A)

private theorem scaled_coordinate_eq {R : Type*} [Semigroup R] {f g t x y : R}
    (hu : f * t = g) (hx : x = t * y) : f * x = g * y := by
  rw [hx, ← mul_assoc, hu]

set_option maxHeartbeats 1600000 in
private theorem cross (i : Fin 3) : (localFrame z hz i false).Compatible (localFrame z hz i true) := by
  intro A h₀ h₁ s
  have hA := (le_inf (h₀.trans inf_le_right) (h₁.trans inf_le_right)).trans hQ.ge
  have h := TwistedModule.linearFrame_transition C.sheaf U V Q hQ (t^7) A hA s
  have hu := congrArg Units.val (factor_cross z hz i A (h₀.trans inf_le_left)
    (h₀.trans inf_le_right) (h₁.trans inf_le_right))
  change (factor z hz false i A (h₀.trans inf_le_left) (h₀.trans inf_le_right) : Γ(C,A)) *
    (show Γ(C,A) from (raw false).app A (h₀.trans inf_le_right) s) =
    (factor z hz true i A (h₁.trans inf_le_left) (h₁.trans inf_le_right) : Γ(C,A)) *
      (show Γ(C,A) from (raw true).app A (h₁.trans inf_le_right) s)
  exact scaled_coordinate_eq (R := Γ(C,A))
    (t := (show Γ(C,A) from Twisted.res C.sheaf hA (Units.val (t^7)))) hu h

private theorem compat (i : Fin 3) (a b : Bool) : (localFrame z hz i a).Compatible (localFrame z hz i b) := by
  cases a <;> cases b
  · intro A h₀ h₁ s; rfl
  · exact cross z hz i
  · intro A h₀ h₁ s; exact (cross z hz i A h₁ h₀ s).symm
  · intro A h₀ h₁ s; rfl

private theorem cover (i : Fin 3) : j z hz ⁻¹ᵁ Patch i ≤ ⨆ b, parts z hz i b := by
  rw [← inf_iSup_eq, iSup_bool_eq]
  change _ ≤ _ ⊓ (V ⊔ U)
  rw [sup_comm V U, projective_twoOpen_cover 57 1 (by norm_num), inf_top_eq]

/-- Trivialization on every subopen of the preimage of a spatial coordinate patch. -/
def componentFrame (i : Fin 3) : LocalFrame C.sheaf N (j z hz ⁻¹ᵁ Patch i) :=
  CycleQ2LocalFrameGluing.Cover.gluePatchIso N _ _ (parts z hz i) (cover z hz i) (localFrame z hz i) (compat z hz i)

private theorem componentFrame_local (i : Fin 3) (b : Bool) (A : C.Opens)
    (hi : A ≤ j z hz ⁻¹ᵁ Patch i) (hq : A ≤ quartic b) (s : N.val.obj (op A)) :
    (componentFrame z hz i).app A hi s = (localFrame z hz i b).app A (le_inf hi hq) s :=
  CycleQ2LocalFrameGluing.Cover.mapSection_of_le N _ _ (parts z hz i) (cover z hz i)
    (localFrame z hz i) (compat z hz i) A hi b (le_inf hi hq) s

private theorem local_change (i k : Fin 3) (b : Bool) (A : C.Opens)
    (hi : A ≤ j z hz ⁻¹ᵁ Patch i) (hk : A ≤ j z hz ⁻¹ᵁ Patch k)
    (hq : A ≤ quartic b) (s : N.val.obj (op A)) :
    (show Γ(C,A) from (componentFrame z hz k).app A hk s) = (pulledUnit z hz i k A hi hk : Γ(C,A)) ^ 7 *
      (show Γ(C,A) from (componentFrame z hz i).app A hi s) := by
  rw [componentFrame_local z hz k b A hk hq, componentFrame_local z hz i b A hi hq]
  have h := congrArg Units.val (pulledUnit_cocycle z hz (idx b) i k A (hq.trans (quartic_le z hz b)) hi hk)
  change _ * _ = _ at h
  let a : Γ(C,A) := (raw b).app A hq s
  let hb := hq.trans (quartic_le z hz b)
  change ((pulledUnit z hz (idx b) k A hb hk : Γ(C,A))^7 * (gauge z hz b A : Γ(C,A))) * a =
    (pulledUnit z hz i k A hi hk : Γ(C,A))^7 *
    (((pulledUnit z hz (idx b) i A hb hi : Γ(C,A))^7 * (gauge z hz b A : Γ(C,A))) * a)
  rw [← h, mul_pow]
  ring

/-- The transition is the seventh power of the actual pulled surface unit
on every common subopen, in the orientation of the pole coordinate. -/
theorem componentFrame_change (i k : Fin 3) (A : C.Opens) (hi : A ≤ j z hz ⁻¹ᵁ Patch i)
    (hk : A ≤ j z hz ⁻¹ᵁ Patch k) (s : N.val.obj (op A)) :
    (show Γ(C,A) from (componentFrame z hz k).app A hk s) =
      (pulledUnit z hz i k A hi hk : Γ(C,A)) ^ 7 * (show Γ(C,A) from (componentFrame z hz i).app A hi s) := by
  have hc : A ≤ ⨆ b : Bool, A ⊓ quartic b := by
    rw [← inf_iSup_eq, iSup_bool_eq]
    change _ ≤ _ ⊓ (V ⊔ U)
    rw [sup_comm V U, projective_twoOpen_cover 57 1 (by norm_num), inf_top_eq]
  apply C.sheaf.eq_of_locally_eq' (fun b : Bool => A ⊓ quartic b) A (fun _ => homOfLE inf_le_left) hc
  intro b
  let B := A ⊓ quartic b
  let h : B ≤ A := inf_le_left
  have he := local_change z hz i k b B (h.trans hi) (h.trans hk) inf_le_right (N.val.map (homOfLE h).op s)
  have hu := congrArg Units.val (pulledUnit_restrict z hz i k A B h hi hk)
  change Twisted.res C.sheaf h (show Γ(C,A) from (componentFrame z hz k).app A hk s) =
    Twisted.res C.sheaf h ((pulledUnit z hz i k A hi hk : Γ(C,A))^7 *
      (show Γ(C,A) from (componentFrame z hz i).app A hi s))
  rw [map_mul, map_pow]
  exact ((componentFrame z hz k).naturality h hk s).trans (he.trans
    (congrArg₂ (fun a b : Γ(C,B) => a * b) (congrArg (fun a : Γ(C,B) => a ^ 7) hu.symm)
      ((componentFrame z hz i).naturality h hi s).symm))

/-- On a surface overlap the frame change is the image of its own
transition unit under the actual morphism of structure sheaves. -/
theorem componentFrame_change_on (i k : Fin 3) (P : Surface.Opens) (A : C.Opens)
    (hi : P ≤ Patch i) (hk : P ≤ Patch k) (ha : A ≤ j z hz ⁻¹ᵁ P)
    (s : N.val.obj (op A)) :
    (show Γ(C,A) from (componentFrame z hz k).app A (ha.trans ((j z hz).preimage_mono hk)) s) =
      (j z hz).appLE P A ha (transitionUnit i k P hi hk : Γ(Surface,P)) ^ 7 *
        (show Γ(C,A) from (componentFrame z hz i).app A (ha.trans ((j z hz).preimage_mono hi)) s) := by
  rw [componentFrame_change z hz i k A (ha.trans ((j z hz).preimage_mono hi))]
  exact congrArg (fun u : Γ(C,A)ˣ => (u : Γ(C,A))^7 *
    (show Γ(C,A) from (componentFrame z hz i).app A (ha.trans ((j z hz).preimage_mono hi)) s))
    (pulledUnit_on z hz i k P A hi hk ha).symm

end CycleQ2LiteralOrbitCurveTwistFrames
end

#print axioms CycleQ2LiteralOrbitCurveTwistFrames.componentFrame
#print axioms CycleQ2LiteralOrbitCurveTwistFrames.componentFrame_change

#print axioms CycleQ2LiteralOrbitCurveTwistFrames.componentFrame_change_on
