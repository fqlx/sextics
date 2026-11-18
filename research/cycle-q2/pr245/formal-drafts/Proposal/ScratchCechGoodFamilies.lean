import Mathlib.Algebra.Category.Grp.Preadditive
import Mathlib.Algebra.Homology.HomologicalComplex
import Mathlib.CategoryTheory.Category.Preorder

/-! Extend a complex on a basis by compatible families over good subopens. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory Opposite

namespace CycleQ2.Cech.GoodFamilies

variable {L : Type} [Preorder L] (B : L → Prop)

abbrev Subopen (W : L) := {V : L // B V ∧ V ≤ W}

variable (P : Lᵒᵖ ⥤ AddCommGrpCat.{0})

def sections (W : L) : AddSubgroup (∀ V : Subopen B W, P.obj (op V.1)) where
  carrier s := ∀ V V' : Subopen B W, ∀ h : V.1 ≤ V'.1,
    P.map (homOfLE h).op (s V') = s V
  zero_mem' V V' h := map_zero (P.map (homOfLE h).op).hom
  add_mem' {s t} hs ht V V' h := by
    change P.map (homOfLE h).op (s V' + t V') = s V + t V
    rw [map_add, hs V V' h, ht V V' h]
  neg_mem' {s} hs V V' h := by
    change P.map (homOfLE h).op (-s V') = -s V
    rw [map_neg, hs V V' h]

private def inc {U W : L} (h : U ≤ W) (V : Subopen B U) : Subopen B W :=
  ⟨V.1,V.2.1,V.2.2.trans h⟩

def restrict {U W : L} (h : U ≤ W) : sections B P W →+ sections B P U where
  toFun s := ⟨fun V => s.1 (inc B h V), fun V V' e => s.2 (inc B h V) (inc B h V') e⟩
  map_zero' := rfl
  map_add' _ _ := rfl

def presheaf : Lᵒᵖ ⥤ AddCommGrpCat.{0} where
  obj W := AddCommGrpCat.of (sections B P W.unop)
  map g := AddCommGrpCat.ofHom (restrict B P g.unop.le)
  map_id W := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    intro x; apply Subtype.ext; funext V; rfl
  map_comp f g := rfl

/-- Any ordinary section gives a compatible family of its restrictions. -/
def ofSection (W : L) : P.obj (op W) →+ sections B P W where
  toFun s := ⟨fun V => P.map (homOfLE V.2.2).op s, fun V V' h => by
    change (P.map ((homOfLE V'.2.2).op) ≫ P.map (homOfLE h).op) s = _
    rw [← P.map_comp]; rfl⟩
  map_zero' := by apply Subtype.ext; funext V; exact map_zero _
  map_add' s t := by apply Subtype.ext; funext V; exact map_add _ s t

def unit : P ⟶ presheaf B P where
  app W := AddCommGrpCat.ofHom (ofSection B P W.unop)
  naturality {W U} g := by
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    intro x; apply Subtype.ext; funext V
    change (P.map g ≫ P.map (homOfLE V.2.2).op) x = _
    rw [← P.map_comp]; rfl

def evaluate (W : L) (hW : B W) : sections B P W →+ P.obj (op W) where
  toFun s := s.1 ⟨W,hW,le_rfl⟩
  map_zero' := rfl
  map_add' _ _ := rfl

@[simp] theorem evaluate_ofSection (W : L) (hW : B W) (x : P.obj (op W)) :
    evaluate B P W hW (ofSection B P W x) = x := by
  change P.map (𝟙 (op W)) x = x
  rw [P.map_id]; rfl

@[simp] theorem ofSection_evaluate (W : L) (hW : B W) (s : sections B P W) :
    ofSection B P W (evaluate B P W hW s) = s := by
  apply Subtype.ext; funext V
  exact s.2 V ⟨W,hW,le_rfl⟩ V.2.2

theorem unit_isIso (W : L) (hW : B W) : IsIso ((unit B P).app (op W)) := by
  refine ⟨⟨AddCommGrpCat.ofHom (evaluate B P W hW), ?_, ?_⟩⟩
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    exact evaluate_ofSection B P W hW
  · apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    exact ofSection_evaluate B P W hW

/-- A differential only defined and natural on good opens. -/
structure LocalMap (Q : Lᵒᵖ ⥤ AddCommGrpCat.{0}) where
  app (W : L) (hW : B W) : P.obj (op W) →+ Q.obj (op W)
  natural (U W : L) (hU : B U) (hW : B W) (h : U ≤ W) (s : P.obj (op W)) :
    Q.map (homOfLE h).op (app W hW s) = app U hU (P.map (homOfLE h).op s)

variable {P} {Q : Lᵒᵖ ⥤ AddCommGrpCat.{0}} (d : LocalMap B P Q)

def extendAt (W : L) : sections B P W →+ sections B Q W where
  toFun s := ⟨fun V => d.app V.1 V.2.1 (s.1 V), fun V V' h => by
    rw [d.natural, s.2 V V' h]⟩
  map_zero' := by apply Subtype.ext; funext V; exact map_zero _
  map_add' s t := by apply Subtype.ext; funext V; exact map_add _ _ _

def extend : presheaf B P ⟶ presheaf B Q where
  app W := AddCommGrpCat.ofHom (extendAt B d W.unop)
  naturality g := rfl

theorem extend_unit (W : L) (hW : B W) (s : P.obj (op W)) :
    (extend B d).app (op W) ((unit B P).app (op W) s) =
      (unit B Q).app (op W) (d.app W hW s) := by
  apply Subtype.ext; funext V
  exact (d.natural V.1 W V.2.1 hW V.2.2 s).symm

variable (A : ℕ → Lᵒᵖ ⥤ AddCommGrpCat.{0})
    (δ : ∀ n, LocalMap B (A n) (A (n+1)))
    (dsq : ∀ n W h a, (δ (n+1)).app W h ((δ n).app W h a) = 0)

/-- A genuinely defined complex on all opens. Each derivative is computed
on the good subopens. -/
def complex : CochainComplex (Lᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ :=
  CochainComplex.of (fun n => presheaf B (A n)) (fun n => extend B (δ n)) (fun n => by
    apply NatTrans.ext; funext W
    apply AddCommGrpCat.hom_ext; apply AddMonoidHom.ext
    intro s; apply Subtype.ext; funext V
    exact dsq n V.1 V.2.1 (s.1 V))

@[simp] theorem complex_d (n : ℕ) :
    (complex B A δ dsq).d n (n+1) = extend B (δ n) := CochainComplex.of_d _ _ n

end CycleQ2.Cech.GoodFamilies
end

#print axioms CycleQ2.Cech.GoodFamilies.unit_isIso
#print axioms CycleQ2.Cech.GoodFamilies.complex
