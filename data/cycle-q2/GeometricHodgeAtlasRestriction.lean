import Proposal.GeometricHodgeAtlasFrames

/-!
# Restriction of an atlas line along a scheme morphism

Pulling back the transition units on each overlap gives a line on the
inverse-image atlas. Mapping every component of a compatible tuple by the
structure morphism defines the restriction to its direct image.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeAtlasLine

open AlgebraicGeometry CategoryTheory Opposite
open CycleQ2SeedSectionSheafLocal (moduleRes moduleRes_app)

variable {X Y : Scheme.{0}} (f : X ⟶ Y) {I : Type} {U : I → Y.Opens} (g : Transition U)

private def pullUnit (i j : I) (W : X.Opens)
    (hi : W ≤ f ⁻¹ᵁ U i) (hj : W ≤ f ⁻¹ᵁ U j) : Γ(X,W)ˣ :=
  Units.map (f.appLE (U i ⊓ U j) W (le_inf hi hj)).hom.toMonoidHom
    (g.unit i j _ inf_le_left inf_le_right)

private theorem pullUnit_on (i j : I) (V : Y.Opens) (W : X.Opens)
    (hi : V ≤ U i) (hj : V ≤ U j) (hW : W ≤ f ⁻¹ᵁ V) :
    pullUnit f g i j W (hW.trans (f.preimage_mono hi)) (hW.trans (f.preimage_mono hj)) =
      Units.map (f.appLE V W hW).hom.toMonoidHom (g.unit i j V hi hj) := by
  apply Units.ext
  have hr := congrArg Units.val (g.restrict i j inf_le_left inf_le_right (le_inf hi hj))
  change restrictRing (X := Y) _ _ = _ at hr
  change f.appLE (U i ⊓ U j) W _ _ = f.appLE V W _ _
  rw [← hr]
  exact (ConcreteCategory.congr_hom (f.map_appLE hW (homOfLE (le_inf hi hj)).op)
    (g.unit i j (U i ⊓ U j) inf_le_left inf_le_right : Γ(Y,_))).symm

/-- The transition functions on the inverse images of the coordinate opens. -/
def pulled : Transition (fun i => f ⁻¹ᵁ U i) where
  unit := pullUnit f g
  self i W hi := by
    rw [pullUnit_on f g i i (U i) W le_rfl le_rfl hi, g.self, map_one]
  compose i j k W hi hj hk := by
    let V := U i ⊓ (U j ⊓ U k)
    have hW : W ≤ f ⁻¹ᵁ V := le_inf hi (le_inf hj hk)
    have h₁ : V ≤ U i := inf_le_left
    have h₂ : V ≤ U j := inf_le_right.trans inf_le_left
    have h₃ : V ≤ U k := inf_le_right.trans inf_le_right
    rw [pullUnit_on f g i j V W h₁ h₂ hW, pullUnit_on f g j k V W h₂ h₃ hW,
      pullUnit_on f g i k V W h₁ h₃ hW, ← map_mul, g.compose]
  restrict i j {V W} hi hj hW := by
    apply Units.ext
    exact ConcreteCategory.congr_hom (C := CommRingCat)
      (f.appLE_map (show _ ≤ f ⁻¹ᵁ (U i ⊓ U j) from le_inf hi hj) (homOfLE hW).op)
      (g.unit i j (U i ⊓ U j) inf_le_left inf_le_right : Γ(Y,_))

/-- The transition on any source subopen is the image of the transition
on any common target chart containing that subopen's image. -/
theorem pulled_unit_on (i j : I) (V : Y.Opens) (W : X.Opens)
    (hi : V ≤ U i) (hj : V ≤ U j) (hW : W ≤ f ⁻¹ᵁ V) :
    ((pulled f g).unit i j W (hW.trans (f.preimage_mono hi)) (hW.trans (f.preimage_mono hj))).val =
      f.appLE V W hW (g.unit i j V hi hj).val :=
  congrArg Units.val (pullUnit_on f g i j V W hi hj hW)

theorem pulled_unit_preimage (i j : I) (V : Y.Opens) (hi : V ≤ U i) (hj : V ≤ U j) :
    ((pulled f g).unit i j (f ⁻¹ᵁ V) (f.preimage_mono hi) (f.preimage_mono hj) : Γ(X,_)) =
      f.app V (g.unit i j V hi hj : Γ(Y,V)) := by
  exact (congrArg Units.val (pullUnit_on f g i j V (f ⁻¹ᵁ V) hi hj le_rfl)).trans
    (ConcreteCategory.congr_hom (f.appLE_eq_app (U := V)) (g.unit i j V hi hj : Γ(Y,V)))

private theorem restrict_app {V W : Y.Opens} (h : W ≤ V) (a : Γ(Y,V)) :
    restrictRing (X := X) (f.preimage_mono h) (f.app V a) = f.app W (restrictRing h a) :=
  (ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) a).symm

private def restrictTuple (V : Y.Opens) (s : Γ(line g,V)) : Γ(line (pulled f g),f ⁻¹ᵁ V) := by
  refine pack (pulled f g) _ (fun i => f.app (V ⊓ U i) (component g i V s)) ?_
  intro i j
  let W := triple (U := U) V i j
  have h₁ : W ≤ V ⊓ U i := inf_le_inf_left V inf_le_left
  have h₂ : W ≤ V ⊓ U j := inf_le_inf_left V inf_le_right
  refine (restrict_app f h₁ (component g i V s)).trans ?_
  refine (congrArg (f.app W) (component_compatible g V s i j)).trans ?_
  refine (map_mul (f.app W).hom _ _).trans ?_
  exact congrArg₂ (fun a b : Γ(X,f ⁻¹ᵁ W) => a * b)
    (pulled_unit_preimage f g i j W (inf_le_right.trans inf_le_left) (inf_le_right.trans inf_le_right)).symm
    (restrict_app f h₂ (component g j V s)).symm

private theorem component_restrictTuple (V : Y.Opens) (s : Γ(line g,V)) (i : I) :
    component (pulled f g) i (f ⁻¹ᵁ V) (restrictTuple f g V s) =
      f.app (V ⊓ U i) (component g i V s) := component_pack ..

private theorem component_scale {Z : Scheme.{0}} {P : I → Z.Opens} (d : Transition P)
    (i : I) (V : Z.Opens) (a : Γ(Z,V)) (s : Γ(line d,V)) :
    component d i V (a • s) = restrictRing (X := Z) inf_le_left a * component d i V s :=
  ((projection d i).val.app (op V)).hom.map_smul a s

private theorem component_res {Z : Scheme.{0}} {P : I → Z.Opens} (d : Transition P)
    (i : I) {V W : Z.Opens} (h : W ≤ V) (s : Γ(line d,V)) :
    component d i W (moduleRes _ h s) =
      restrictRing (X := Z) (inf_le_inf_right _ h) (component d i V s) :=
  (moduleRes_app (projection d i) h s).symm

private def restrictLinear (V : Y.Opens) :
    Γ(line g,V) →ₗ[Γ(Y,V)] Γ((Scheme.Modules.pushforward f).obj (line (pulled f g)),V) where
  toFun := restrictTuple f g V
  map_add' s t := by
    apply component_injective (pulled f g)
    intro i
    change component _ i _ (restrictTuple f g V (s+t)) =
      (projection _ i).app _ (restrictTuple f g V s + restrictTuple f g V t)
    rw [map_add, component_restrictTuple]
    change f.app _ ((projection _ i).app _ (s+t)) =
      component _ i _ (restrictTuple f g V s) + component _ i _ (restrictTuple f g V t)
    rw [map_add, map_add, component_restrictTuple, component_restrictTuple]
    rfl
  map_smul' a s := by
    apply component_injective (pulled f g)
    intro i
    change component _ i _ (restrictTuple f g V (a • s)) =
      component _ i _ (f.app V a • restrictTuple f g V s)
    rw [component_restrictTuple, component_scale, component_scale, component_restrictTuple, map_mul]
    exact congrArg (fun b : Γ(X,f ⁻¹ᵁ (V ⊓ U i)) => b * f.app _ (component g i V s))
      (restrict_app f (show V ⊓ U i ≤ V from inf_le_left) a).symm

/-- Restrict a section of the atlas line along the scheme morphism. -/
def restrictLine : line g ⟶ (Scheme.Modules.pushforward f).obj (line (pulled f g)) where
  val.app V := ConcreteCategory.ofHom (C := ModuleCat _) (restrictLinear f g V.unop)
  val.naturality {V W} e := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    apply component_injective (pulled f g)
    intro i
    let h := leOfHom e.unop
    change component _ i _ (restrictTuple f g W.unop (moduleRes _ h s)) =
      component _ i _ (moduleRes _ (f.preimage_mono h) (restrictTuple f g V.unop s))
    have h' := inf_le_inf_right (U i) h
    refine (component_restrictTuple f g _ _ i).trans ?_
    refine (congrArg (f.app _) (component_res g i h s)).trans ?_
    refine (restrict_app f h' _).symm.trans ?_
    refine (congrArg (restrictRing (X := X) (f.preimage_mono h')) (component_restrictTuple f g _ s i).symm).trans ?_
    exact (component_res (pulled f g) i (f.preimage_mono h) _).symm

/-- In every chart frame restriction is the map on regular functions. -/
theorem restrictLine_frame (i : I) (V : Y.Opens) (hi : V ≤ U i) (s : Γ(line g,V)) :
    frame (pulled f g) i (f ⁻¹ᵁ V) (f.preimage_mono hi) ((restrictLine f g).app V s) =
      f.app V (frame g i V hi s) := by
  change restrictRing (X := X) (f.preimage_mono (le_inf le_rfl hi))
      (component _ i _ (restrictTuple f g V s)) = _
  rw [component_restrictTuple, restrict_app]
  rfl

end CycleQ2HodgeAtlasLine
end

#print axioms CycleQ2HodgeAtlasLine.restrictLine_frame
