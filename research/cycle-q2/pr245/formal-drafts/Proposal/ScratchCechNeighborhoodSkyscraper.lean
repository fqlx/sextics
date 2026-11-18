import Proposal.ScratchCechBasisSheafification
import Mathlib.Topology.Sheaves.Skyscraper
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero

/-! Pointwise evaluation of a sheaf complex via its neighborhood sections. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
noncomputable section
open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat Opposite

namespace CycleQ2.Cech.PointEvaluation

variable {X : TopCat.{0}} (x : X)
local instance (U : Opens X) : Decidable (x ∈ U) := Classical.propDecidable _

variable {P : X.Presheaf AddCommGrpCat.{0}} {A : AddCommGrpCat.{0}}

/-- Neighborhood evaluations that are stable under every further restriction. -/
structure Value (P : X.Presheaf AddCommGrpCat.{0}) (A : AddCommGrpCat.{0}) where
  app (W : Opens X) (hx : x ∈ W) : P.obj (op W) ⟶ A
  natural {W V : Opens X} (h : V ≤ W) (hx : x ∈ V) :
    P.map (homOfLE h).op ≫ app V hx = app W (h hx)

variable {x} (e : Value x P A)

def toSky : P ⟶ skyscraperPresheaf x A where
  app U := if h : x ∈ U.unop then e.app U.unop h ≫ eqToHom (if_pos h).symm
    else (isTerminalSkyscraperSheafObjObjOfNotMem x A h).from _
  naturality U V g := by
    by_cases hV : x ∈ V.unop
    · have hU : x ∈ U.unop := g.unop.le hV
      simp only [dif_pos hU, dif_pos hV, skyscraperPresheaf_map, Category.assoc, eqToHom_trans]
      apply reassoc_of% (e.natural g.unop.le hV)
    · exact (isTerminalSkyscraperSheafObjObjOfNotMem x A hV).hom_ext _ _

@[reassoc] theorem toSky_app (W : Opens X) (hx : x ∈ W) :
    (toSky e).app (op W) ≫ eqToHom (if_pos hx) = e.app W hx := by
  simp [toSky,hx]

abbrev skyComplex (x : X) (D : CochainComplex AddCommGrpCat.{0} ℕ) :=
  ((skyscraperSheafFunctor x).mapHomologicalComplex (ComplexShape.up ℕ)).obj D

variable {M : CochainComplex (X.Presheaf AddCommGrpCat.{0}) ℕ}
    {D : CochainComplex AddCommGrpCat.{0} ℕ} (v : ∀ n, Value x (M.X n) (D.X n))
    (dv : ∀ n (W : Opens X) (hx : x ∈ W),
      (v n).app W hx ≫ D.d n (n+1) = (M.d n (n+1)).app (op W) ≫ (v (n+1)).app W hx)

def toSkyComplex : M ⟶ BasisSheafification.underlyingComplex (skyComplex x D) where
  f n := toSky (v n)
  comm' n m hnm := by
    obtain rfl : n+1 = m := hnm
    apply NatTrans.ext
    funext U
    by_cases hu : x ∈ U.unop
    · change (toSky (v n)).app U ≫ (SkyscraperPresheafFunctor.map' x (D.d n (n+1))).app U =
        (M.d n (n+1)).app U ≫ (toSky (v (n+1))).app U
      simp only [toSky, hu, SkyscraperPresheafFunctor.map'_app, dif_pos,
        Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]
      apply reassoc_of% (dv n U.unop hu)
    · exact (isTerminalSkyscraperSheafObjObjOfNotMem x (D.X (n+1)) hu).hom_ext _ _

def liftSkyComplex : BasisSheafification.sheafComplex X M ⟶ skyComplex x D :=
  BasisSheafification.liftToSheafComplex (toSkyComplex v dv)

/-- On every neighborhood containing the point, the actual sheaf map on an
original section is its specified field value. -/
theorem liftSky_app (n : ℕ) (W : Opens X) (hx : x ∈ W) :
    (toSheafify (BasisSheafification.J X) (M.X n)).app (op W) ≫
      ((liftSkyComplex v dv).f n).hom.app (op W) ≫ eqToHom (if_pos hx) = (v n).app W hx := by
  rw [← Category.assoc]
  change ((toSheafify (BasisSheafification.J X) (M.X n) ≫
    ((liftSkyComplex v dv).f n).hom).app (op W)) ≫ _ = _
  rw [liftSkyComplex,BasisSheafification.toSheafify_lift_f]
  exact toSky_app (v n) W hx

end CycleQ2.Cech.PointEvaluation
end
#print axioms CycleQ2.Cech.PointEvaluation.liftSky_app
