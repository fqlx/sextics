import Proposal.GeometricLiteralOrbitCurveTwistPullback

/-!
# Pullback of degree-seven sections to the three actual curves

The two chart coordinates of a surface section pull back to a compatible
pair on every curve open over its domain. Multiplication by the character
in the second frame gives the gluing law of the original curve twist.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralOrbitCurveTwistSections

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2SeedProjectiveImageCocycle CycleQ2GeometricProjectiveCurve
  CycleQ2LiteralMovingPoleComponents CycleQ2LiteralOrbitCurveTwistPullback
  CycleQ2LiteralCurvePositiveTwist CycleQ2SeedSectionSheafLocal
  CycleQ2LiteralMovingIdealExact CycleQ2SeedSectionSheafGlobal

private abbrev Curve := projectiveCurve 57 1
private abbrev U := firstProjectivePatch 57 1
private abbrev T := secondProjectivePatch 57 1
private abbrev Q := overlapProjectivePatch 57 1
private abbrev hQ := overlapProjectivePatch_eq 57 1
private abbrev t := projectiveTransitionUnit 57 1 ^ 7
private abbrev M := ambientTwist 7

variable (z : ℂ) (hz : z ^ 3 = 1)
private abbrev j := componentImmersion z hz

/-- Evaluate a section in its surface chart frame and then pull this regular
function back by the translated curve immersion. -/
def chartValue (i : Fin 3) (V : Surface.Opens) (A : Curve.Opens)
    (ha : A ≤ j z hz ⁻¹ᵁ V) (hi : A ≤ j z hz ⁻¹ᵁ Patch i) : Γ(M,V) →+ Γ(Curve,A) :=
  ((j z hz).appLE (V ⊓ Patch i) A (le_inf ha hi)).hom.toAddMonoidHom.comp
    ((coordinate 7 i _ inf_le_right).toAddMonoidHom.comp (moduleRes M inf_le_left))

private theorem chartValue_restrict (i : Fin 3) (V : Surface.Opens) (A B : Curve.Opens)
    (ha : A ≤ j z hz ⁻¹ᵁ V) (hi : A ≤ j z hz ⁻¹ᵁ Patch i) (hBA : B ≤ A) (x : Γ(M,V)) :
    Twisted.res Curve.sheaf hBA (chartValue z hz i V A ha hi x) =
      chartValue z hz i V B (hBA.trans ha) (hBA.trans hi) x :=
  ConcreteCategory.congr_hom ((j z hz).appLE_map (le_inf ha hi :
    A ≤ j z hz ⁻¹ᵁ (V ⊓ Patch i)) (homOfLE hBA).op) _

private theorem chartValue_on (i : Fin 3) (V P : Surface.Opens) (A : Curve.Opens)
    (hPV : P ≤ V) (hP : P ≤ Patch i) (ha : A ≤ j z hz ⁻¹ᵁ P) (x : Γ(M,V)) :
    (j z hz).appLE P A ha (coordinate 7 i P hP (moduleRes M hPV x)) =
      chartValue z hz i V A (ha.trans ((j z hz).preimage_mono hPV))
        (ha.trans ((j z hz).preimage_mono hP)) x := by
  let h := le_inf hPV hP
  have v := coordinate_restrict 7 i h (show V ⊓ Patch i ≤ Patch i from inf_le_right)
    (moduleRes M inf_le_left x)
  rw [moduleRes_comp] at v
  rw [← v]
  exact ConcreteCategory.congr_hom ((j z hz).map_appLE ha (homOfLE h).op) _

private theorem first_le : U ≤ j z hz ⁻¹ᵁ Patch 0 := by
  rw [component_preimage_patch]
  exact CycleQ2GeometricProjectiveAffine.firstProjectivePatch_le_firstCoordinate 57 1

private theorem second_le : T ≤ j z hz ⁻¹ᵁ Patch 1 := by
  rw [component_preimage_patch]
  exact CycleQ2GeometricProjectiveAffine.secondProjectivePatch_le_secondCoordinate 57 1

variable (V : Surface.Opens) (W : Curve.Opens) (hWV : W ≤ j z hz ⁻¹ᵁ V)

def firstValue : Γ(M,V) →+ Γ(Curve,W ⊓ U) :=
  chartValue z hz 0 V (W ⊓ U) (inf_le_left.trans hWV) (inf_le_right.trans (first_le z hz))

def secondValue : Γ(M,V) →+ Γ(Curve,W ⊓ T) :=
  (AddMonoidHom.mulLeft (curveScalar (W ⊓ T) z)).comp
    (chartValue z hz 1 V (W ⊓ T) (inf_le_left.trans hWV) (inf_le_right.trans (second_le z hz)))

set_option maxHeartbeats 1200000 in
private theorem pair_mem (x : Γ(M,V)) :
    (firstValue z hz V W hWV x, secondValue z hz V W hWV x) ∈
      Twisted.Pairs Curve.sheaf U T Q hQ t W := by
  let P := V ⊓ (Patch 0 ⊓ Patch 1)
  let A := W ⊓ Q
  have ha : A ≤ j z hz ⁻¹ᵁ P :=
    le_inf (inf_le_left.trans hWV) (inf_le_right.trans (quarticOverlap_le_component_preimage z hz))
  have h₀ : P ≤ Patch 0 := inf_le_right.trans inf_le_left
  have h₁ : P ≤ Patch 1 := inf_le_right.trans inf_le_right
  have he := component_coordinate z hz P h₀ h₁ A inf_le_right ha (moduleRes M inf_le_left x)
  rw [chartValue_on z hz 0 V P A inf_le_left h₀ ha x,
    chartValue_on z hz 1 V P A inf_le_left h₁ ha x] at he
  let hA₀ := inf_le_inf_left W (hQ.le.trans (inf_le_left : U ⊓ T ≤ U))
  let hA₁ := inf_le_inf_left W (hQ.le.trans (inf_le_right : U ⊓ T ≤ T))
  apply sub_eq_zero.mpr
  change Twisted.res Curve.sheaf hA₀ (chartValue z hz 0 V (W ⊓ U) (inf_le_left.trans hWV) (inf_le_right.trans (first_le z hz)) x) =
    Twisted.res Curve.sheaf (show W ⊓ Q ≤ Q from inf_le_right) (t : Γ(Curve,Q)) *
      Twisted.res Curve.sheaf hA₁ (curveScalar (W ⊓ T) z * chartValue z hz 1 V (W ⊓ T) (inf_le_left.trans hWV) (inf_le_right.trans (second_le z hz)) x)
  rw [chartValue_restrict, map_mul, chartValue_restrict]
  rw [show Twisted.res Curve.sheaf hA₁ (curveScalar (W ⊓ T) z) = curveScalar A z from
    CycleQ2GeometricTwistedDifferential.coefficientOn_restrict _ _ hA₁ z]
  exact he

/-- Pullback on arbitrary surface and curve opens. Its two coordinates
are the actual pulled functions, with the second frame rescaled by z. -/
def sectionPullback : Γ(M,V) →+ (curveTwistModule 7).val.obj (op W) :=
  (Twisted.sectionPairsEquiv Curve.sheaf U T Q hQ t W).symm.toAddMonoidHom.comp
    (((firstValue z hz V W hWV).prod (secondValue z hz V W hWV)).codRestrict _
      (pair_mem z hz V W hWV))

theorem sectionPullback_coordinates (x : Γ(M,V)) :
    ((Twisted.sectionPairsEquiv Curve.sheaf U T Q hQ t W)
      (sectionPullback z hz V W hWV x)).val =
      (firstValue z hz V W hWV x, secondValue z hz V W hWV x) :=
  congrArg Subtype.val ((Twisted.sectionPairsEquiv Curve.sheaf U T Q hQ t W).apply_symm_apply _)

private theorem chartValue_naturality (i : Fin 3) (V' : Surface.Opens) (hV' : V' ≤ V)
    (B : Curve.Opens) (hBW : B ≤ W) (hb : B ≤ j z hz ⁻¹ᵁ V')
    (hi : W ≤ j z hz ⁻¹ᵁ Patch i) (x : Γ(M,V)) :
    chartValue z hz i V' B hb (hBW.trans hi) (moduleRes M hV' x) =
      Twisted.res Curve.sheaf hBW (chartValue z hz i V W hWV hi x) := by
  let hp := inf_le_inf_right (Patch i) hV'
  let hx := coordinate 7 i (V ⊓ Patch i) inf_le_right (moduleRes M inf_le_left x)
  have h := coordinate_restrict 7 i hp (show V ⊓ Patch i ≤ Patch i from inf_le_right)
    (moduleRes M inf_le_left x)
  rw [moduleRes_comp] at h
  change (j z hz).appLE (V' ⊓ Patch i) B _ (coordinate 7 i _ inf_le_right
    (moduleRes M inf_le_left (moduleRes M hV' x))) = _
  rw [moduleRes_comp, ← h]
  exact CycleQ2ChartSectionPullback.restriction_square (j z hz) hp (le_inf hWV hi) hBW
    (le_inf hb (hBW.trans hi)) hx

/-- The pulled section commutes with restriction of both its source open
and its curve open. -/
theorem sectionPullback_restrict (V' : Surface.Opens) (hV' : V' ≤ V)
    (W' : Curve.Opens) (hW' : W' ≤ W) (hw : W' ≤ j z hz ⁻¹ᵁ V') (x : Γ(M,V)) :
    sectionPullback z hz V' W' hw (moduleRes M hV' x) =
      (curveTwistModule 7).val.map (homOfLE hW').op (sectionPullback z hz V W hWV x) := by
  apply (Twisted.sectionPairsEquiv Curve.sheaf U T Q hQ t W').injective
  apply Subtype.ext
  apply Prod.ext
  · refine Eq.trans ?_ (Twisted.sectionPairs_fst_naturality Curve.sheaf U T Q hQ t hW' (sectionPullback z hz V W hWV x)).symm
    rw [sectionPullback_coordinates, sectionPullback_coordinates]
    exact chartValue_naturality z hz V (W ⊓ U) (inf_le_left.trans hWV) 0 V' hV'
      (W' ⊓ U) (inf_le_inf_right U hW') (inf_le_left.trans hw) (inf_le_right.trans (first_le z hz)) x
  · refine Eq.trans ?_ (Twisted.sectionPairs_snd_naturality Curve.sheaf U T Q hQ t hW' (sectionPullback z hz V W hWV x)).symm
    rw [sectionPullback_coordinates, sectionPullback_coordinates]
    change curveScalar (W' ⊓ T) z * chartValue z hz 1 V' (W' ⊓ T) (inf_le_left.trans hw) (inf_le_right.trans (second_le z hz)) (moduleRes M hV' x) =
      Twisted.res Curve.sheaf (inf_le_inf_right T hW') (curveScalar (W ⊓ T) z * chartValue z hz 1 V (W ⊓ T) (inf_le_left.trans hWV) (inf_le_right.trans (second_le z hz)) x)
    rw [map_mul, show Twisted.res Curve.sheaf (inf_le_inf_right T hW') (curveScalar (W ⊓ T) z) =
      curveScalar (W' ⊓ T) z from CycleQ2GeometricTwistedDifferential.coefficientOn_restrict _ _ _ z]
    exact congrArg (curveScalar (W' ⊓ T) z * ·) (chartValue_naturality z hz V (W ⊓ T)
      (inf_le_left.trans hWV) 1 V' hV' (W' ⊓ T) (inf_le_inf_right T hW')
      (inf_le_left.trans hw) (inf_le_right.trans (second_le z hz)) x)

private theorem chartValue_smul (i : Fin 3) (hi : W ≤ j z hz ⁻¹ᵁ Patch i)
    (a : Γ(Surface,V)) (x : Γ(M,V)) :
    chartValue z hz i V W hWV hi (a • x) =
      (j z hz).appLE V W hWV a * chartValue z hz i V W hWV hi x := by
  change (j z hz).appLE (V ⊓ Patch i) W _ (coordinate 7 i _ inf_le_right
    (moduleRes M inf_le_left (a • x))) = _
  have hs : moduleRes M (show V ⊓ Patch i ≤ V from inf_le_left) (a • x) =
      targetRes inf_le_left a • moduleRes M inf_le_left x := M.map_smul _ a x
  rw [hs, map_smul, smul_eq_mul, map_mul]
  exact congrArg (· * chartValue z hz i V W hWV hi x)
    (ConcreteCategory.congr_hom ((j z hz).map_appLE (le_inf hWV hi :
      W ≤ j z hz ⁻¹ᵁ (V ⊓ Patch i)) (homOfLE (show V ⊓ Patch i ≤ V from inf_le_left)).op) a)

local instance (O : Curve.Opens) : Module Γ(Curve,O) ((curveTwistModule 7).val.obj (op O)) :=
  ((curveTwistModule 7).val.obj (op O)).isModule

theorem sectionPullback_smul (a : Γ(Surface,V)) (x : Γ(M,V)) :
    sectionPullback z hz V W hWV (a • x) =
      (j z hz).appLE V W hWV a • sectionPullback z hz V W hWV x := by
  apply (Twisted.sectionPairsEquiv Curve.sheaf U T Q hQ t W).injective
  apply Subtype.ext
  apply Prod.ext
  · refine Eq.trans ?_ (TwistedModule.sectionPairs_fst_smul Curve.sheaf U T Q hQ t W ((j z hz).appLE V W hWV a) (sectionPullback z hz V W hWV x)).symm
    rw [sectionPullback_coordinates, sectionPullback_coordinates]
    change chartValue z hz 0 V (W ⊓ U) (inf_le_left.trans hWV) (inf_le_right.trans (first_le z hz)) (a • x) =
      (show Γ(Curve,W ⊓ U) from Twisted.res Curve.sheaf (show W ⊓ U ≤ W from inf_le_left) ((j z hz).appLE V W hWV a)) *
      chartValue z hz 0 V (W ⊓ U) (inf_le_left.trans hWV) (inf_le_right.trans (first_le z hz)) x
    rw [chartValue_smul]
    exact congrArg (· * chartValue z hz 0 V (W ⊓ U) (inf_le_left.trans hWV) (inf_le_right.trans (first_le z hz)) x)
      (ConcreteCategory.congr_hom ((j z hz).appLE_map hWV (homOfLE (show W ⊓ U ≤ W from inf_le_left)).op) a).symm
  · refine Eq.trans ?_ (TwistedModule.sectionPairs_snd_smul Curve.sheaf U T Q hQ t W ((j z hz).appLE V W hWV a) (sectionPullback z hz V W hWV x)).symm
    rw [sectionPullback_coordinates, sectionPullback_coordinates]
    change curveScalar (W ⊓ T) z * chartValue z hz 1 V (W ⊓ T) (inf_le_left.trans hWV) (inf_le_right.trans (second_le z hz)) (a • x) =
      (show Γ(Curve,W ⊓ T) from Twisted.res Curve.sheaf (show W ⊓ T ≤ W from inf_le_left) ((j z hz).appLE V W hWV a)) *
        (curveScalar (W ⊓ T) z * chartValue z hz 1 V (W ⊓ T) (inf_le_left.trans hWV) (inf_le_right.trans (second_le z hz)) x)
    have h := ConcreteCategory.congr_hom ((j z hz).appLE_map hWV
      (homOfLE (show W ⊓ T ≤ W from inf_le_left)).op) a
    rw [chartValue_smul, show Twisted.res Curve.sheaf (show W ⊓ T ≤ W from inf_le_left)
      ((j z hz).appLE V W hWV a) = (j z hz).appLE V (W ⊓ T) (inf_le_left.trans hWV) a from h]
    ring

/-- Restriction of the surface twist along the actual component immersion,
expressed by a morphism into the pushforward of the native curve module. -/
def restrictionHom : M ⟶ (Scheme.Modules.pushforward (j z hz)).obj (curveTwistModule 7) where
  val :=
    { app := fun O => by
        let N : Surface.Modules := (Scheme.Modules.pushforward (j z hz)).obj (curveTwistModule 7)
        letI : Module (Surface.ringCatSheaf.obj.obj O) (N.val.obj O) := (N.val.obj O).isModule
        change M.val.obj O ⟶ N.val.obj O
        exact ModuleCat.ofHom (X := M.val.obj O) (Y := N.val.obj O)
          { toFun := sectionPullback z hz O.unop (j z hz ⁻¹ᵁ O.unop) le_rfl
            map_add' := (sectionPullback z hz O.unop _ le_rfl).map_add
            map_smul' := by
              intro a x
              have h := sectionPullback_smul z hz O.unop _ le_rfl a x
              rw [Scheme.Hom.appLE_eq_app] at h
              exact h }
      naturality := by
        intro O P f
        ext x
        exact sectionPullback_restrict z hz O.unop _ le_rfl P.unop f.unop.le _
          ((j z hz).preimage_mono f.unop.le) le_rfl x }

/-- The genuine morphism from the scheme-module pullback of O_D(7). -/
def twistPullback : (Scheme.Modules.pullback (componentImmersion z hz)).obj (ambientTwist 7) ⟶
    (curveTwistModule 7 : Curve.Modules) :=
  ((Scheme.Modules.pullbackPushforwardAdjunction (j z hz)).homEquiv _ _).symm (restrictionHom z hz)

end CycleQ2LiteralOrbitCurveTwistSections
end

#print axioms CycleQ2LiteralOrbitCurveTwistSections.sectionPullback
#print axioms CycleQ2LiteralOrbitCurveTwistSections.sectionPullback_coordinates

#print axioms CycleQ2LiteralOrbitCurveTwistSections.sectionPullback_restrict

#print axioms CycleQ2LiteralOrbitCurveTwistSections.twistPullback
