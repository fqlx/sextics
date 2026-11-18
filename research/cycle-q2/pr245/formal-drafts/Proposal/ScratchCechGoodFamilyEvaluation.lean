import Proposal.ScratchCechGoodFamilies
import Mathlib.Topology.Sets.Opens

/-! Evaluation at a point of a compatible family on a basis, including
arbitrary opens with local coordinate neighborhoods. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open CategoryTheory Opposite TopologicalSpace

namespace CycleQ2.Cech.GoodFamilies

variable {Y : Type} [TopologicalSpace Y] (B : Opens Y → Prop) (hb : Opens.IsBasis {W | B W})
    (x : Y) (P : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}) (A : AddCommGrpCat.{0})

/-- An evaluation on the good neighborhoods of x with values in one group. -/
structure AtPoint where
  value (W : Opens Y) (_ : B W) (_ : x ∈ W) : P.obj (op W) →+ A
  natural {U V : Opens Y} (h : U ≤ V) (hU : B U) (hV : B V) (hx : x ∈ U)
      (s : P.obj (op V)) :
    value U hU hx (P.map (homOfLE h).op s) = value V hV (h hx) s

variable {B x P A} (e : AtPoint B x P A)

private def subAt {W : Opens Y} (hx : x ∈ W) : Subopen B W :=
  let h := Opens.isBasis_iff_nbhd.mp hb hx
  ⟨h.choose,h.choose_spec.1,h.choose_spec.2.2⟩

private theorem mem_subAt {W : Opens Y} (hx : x ∈ W) : x ∈ (subAt hb hx).1 :=
  (Opens.isBasis_iff_nbhd.mp hb hx).choose_spec.2.1

/-- Local values agree after restriction to a common good neighborhood. -/
theorem eval_eq {W : Opens Y} (s : sections B P W) (V V' : Subopen B W)
    (hx : x ∈ V.1) (hx' : x ∈ V'.1) :
    e.value V.1 V.2.1 hx (s.1 V) = e.value V'.1 V'.2.1 hx' (s.1 V') := by
  obtain ⟨D,hD,hxD,hDV⟩ := Opens.isBasis_iff_nbhd.mp hb (show x ∈ V.1 ⊓ V'.1 from ⟨hx,hx'⟩)
  have h : D ≤ V.1 := hDV.trans inf_le_left
  have h' : D ≤ V'.1 := hDV.trans inf_le_right
  let v : Subopen B W := ⟨D,hD,h.trans V.2.2⟩
  calc
    _ = e.value D hD hxD (s.1 v) := by
      rw [← s.2 v V h]
      exact (e.natural h hD V.2.1 hxD _).symm
    _ = _ := by
      rw [← s.2 v V' h']
      exact e.natural h' hD V'.2.1 hxD _

def pointValue {W : Opens Y} (hx : x ∈ W) : sections B P W →+ A where
  toFun s := e.value _ (subAt hb hx).2.1 (mem_subAt hb hx) (s.1 (subAt hb hx))
  map_zero' := map_zero _
  map_add' _ _ := map_add _ _ _

theorem pointValue_at {W : Opens Y} (hx : x ∈ W) (s : sections B P W) (V : Subopen B W)
    (hV : x ∈ V.1) : pointValue hb e hx s = e.value V.1 V.2.1 hV (s.1 V) :=
  eval_eq hb e s _ _ (mem_subAt hb hx) hV

theorem pointValue_natural {W U : Opens Y} (h : U ≤ W) (hx : x ∈ U)
    (s : sections B P W) :
    pointValue hb e hx (restrict B P h s) = pointValue hb e (h hx) s := by
  let V := subAt hb hx
  let V' : Subopen B W := ⟨V.1,V.2.1,V.2.2.trans h⟩
  exact (pointValue_at hb e (h hx) s V' (mem_subAt hb hx)).symm

theorem pointValue_ofSection {W : Opens Y} (hW : B W) (hx : x ∈ W) (s : P.obj (op W)) :
    pointValue hb e hx (ofSection B P W s) = e.value W hW hx s := by
  rw [pointValue_at hb e hx _ (⟨W,hW,le_rfl⟩ : Subopen B W) hx]
  change e.value W hW hx (evaluate B P W hW (ofSection B P W s)) = _
  rw [evaluate_ofSection]

variable {Q : (Opens Y)ᵒᵖ ⥤ AddCommGrpCat.{0}} {A' : AddCommGrpCat.{0}}
    (e' : AtPoint B x Q A') (d : LocalMap B P Q) (D : A →+ A')

theorem pointValue_extend (hd : ∀ W hW hx s, e'.value W hW hx (d.app W hW s) = D (e.value W hW hx s))
    {W : Opens Y} (hx : x ∈ W) (s : sections B P W) :
    pointValue hb e' hx (extendAt B d W s) = D (pointValue hb e hx s) :=
  hd _ _ _ _

end CycleQ2.Cech.GoodFamilies
end
#print axioms CycleQ2.Cech.GoodFamilies.pointValue_natural
#print axioms CycleQ2.Cech.GoodFamilies.pointValue_extend
