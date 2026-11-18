import Proposal.ScratchCechGoodFamilyEvaluation
import Proposal.ScratchCechNeighborhoodSkyscraper
import Proposal.ScratchCechWeightedGoodComplex
import Proposal.ScratchCechKPointSections
import Mathlib.GroupTheory.QuotientGroup.Defs

/-! The map from the proper de Rham sheaf complex to exterior forms at a
specified field-valued point. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace TopCat
open CycleQ2GenericSexticGradient CycleQ2GeometricHodgeThreefold
open CycleQ2LogarithmicChartDerivative (pull pull_d)
open CycleQ2LogarithmicDifferential (exteriorD)
open CycleQ2.Cech.WeightedGoodComplex

namespace CycleQ2.Cech.WeightedFieldEvaluation

variable {k K : Type} [CommRing k] [Field K] [Algebra k K] (φ : CoeffRing →+* k)
    (g : Spec (CommRingCat.of K) ⟶ threefold φ)
    (hg : g ≫ toBase φ = Spec.map (CommRingCat.ofHom (algebraMap k K)))

def atGood (n : ℕ) : GoodFamilies.AtPoint (WeightedBasis.Good φ) (KPoint.point g) (A φ n)
    (CycleQ2LogChartComplex.object k K n) where
  value W _ hx := (pull (KPoint.eval (toBase φ) g hg W hx) n).toAddMonoidHom
  natural {U V} h _ _ hx a := by
    change pull (KPoint.eval (toBase φ) g hg U hx) n
      (pull (((Sections.presheaf (toBase φ)).map (homOfLE h).op).hom) n a) =
      pull (KPoint.eval (toBase φ) g hg V (h hx)) n a
    rw [← CycleQ2LogarithmicPullback.restrict_comp, KPoint.eval_restrict]

variable (hp : IsUnit (φ goodParameter))

def atPoint (n : ℕ) : PointEvaluation.Value (KPoint.point g) ((complex φ).X n)
    (CycleQ2LogChartComplex.object k K n) where
  app _ hx := AddCommGrpCat.ofHom (GoodFamilies.pointValue (WeightedBasis.isBasis φ hp)
    (atGood φ g hg n) hx)
  natural h hx := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    exact GoodFamilies.pointValue_natural (WeightedBasis.isBasis φ hp) (atGood φ g hg n) h hx

theorem atPoint_form (n : ℕ) (W : (threefold φ).Opens) (hW : WeightedBasis.Good φ W)
    (hx : KPoint.point g ∈ W) (a : (A φ n).obj (op W)) :
    (atPoint φ g hg hp n).app W hx ((fromForms φ n).app (op W) a) =
      pull (KPoint.eval (toBase φ) g hg W hx) n a :=
  GoodFamilies.pointValue_ofSection (WeightedBasis.isBasis φ hp) (atGood φ g hg n) hW hx a

variable {I : Type} [LinearOrder I] [Fintype I] (b : Module.Basis I K (KaehlerDifferential k K))
    (x : I → K) (hx : ∀ i, b i = KaehlerDifferential.D k K (x i))

abbrev fieldComplex := CycleQ2LogChartComplex.complex b x hx

theorem atPoint_d (n : ℕ) (W : (threefold φ).Opens) (hw : KPoint.point g ∈ W) :
    (atPoint φ g hg hp n).app W hw ≫ (fieldComplex b x hx).d n (n+1) =
      ((complex φ).d n (n+1)).app (op W) ≫ (atPoint φ g hg hp (n+1)).app W hw := by
  rw [CycleQ2LogChartComplex.complex_d]
  change _ = ((GoodFamilies.complex _ _ _ _).d n (n+1)).app (op W) ≫ _
  rw [GoodFamilies.complex_d]
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact (GoodFamilies.pointValue_extend (WeightedBasis.isBasis φ hp) (atGood φ g hg n)
    (atGood φ g hg (n+1)) (localD φ n) (exteriorD b n)
    (fun V hV ht t => (pull_d (KPoint.eval (toBase φ) g hg V ht) (basis φ hV)
      (coords φ hV) (basis_exact φ hV) b x hx n t).symm) hw s).symm

def evaluate : BasisSheafification.sheafComplex _ (complex φ) ⟶
    PointEvaluation.skyComplex (KPoint.point g) (fieldComplex b x hx) :=
  PointEvaluation.liftSkyComplex (atPoint φ g hg hp) (atPoint_d φ g hg hp b x hx)

abbrev rationalQuotient :=
  AddCommGrpCat.of (CycleQ2LogarithmicPullback.Forms k K 3 ⧸ (exteriorD b 2).range)

def quotientMap : CycleQ2LogChartComplex.object k K 3 ⟶ rationalQuotient b :=
  AddCommGrpCat.ofHom (QuotientAddGroup.mk' (exteriorD b 2).range)

local instance (V : (threefold φ).Opens) : Decidable (KPoint.point g ∈ V) := Classical.propDecidable _

def quotientEvaluation : (BasisSheafification.sheafComplex _ (complex φ)).X 3 ⟶
    skyscraperSheaf (KPoint.point g) (rationalQuotient b) :=
  (evaluate φ g hg hp b x hx).f 3 ≫ (skyscraperSheafFunctor (KPoint.point g)).map (quotientMap b)

/-- Every derivative of a sheaf section of two-forms maps to zero in the
skyscraper of rational three-forms modulo rational exact three-forms. -/
theorem quotientEvaluation_d : (BasisSheafification.sheafComplex _ (complex φ)).d 2 3 ≫
    quotientEvaluation φ g hg hp b x hx = 0 := by
  have hd : (fieldComplex b x hx).d 2 3 ≫ quotientMap b = 0 := by
    rw [CycleQ2LogChartComplex.complex_d]
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro t
    exact (QuotientAddGroup.eq_zero_iff _).2 ⟨t,rfl⟩
  unfold quotientEvaluation
  rw [← Category.assoc, ← (evaluate φ g hg hp b x hx).comm 2 3, Category.assoc]
  change _ ≫ ((skyscraperSheafFunctor (KPoint.point g)).map ((fieldComplex b x hx).d 2 3) ≫
    (skyscraperSheafFunctor (KPoint.point g)).map (quotientMap b)) = 0
  rw [← Functor.map_comp,hd,Functor.map_zero,comp_zero]

/-- The diagram computes the prescribed algebraic pullback on ordinary
forms, with the actual quotient by images of rational two-forms. -/
theorem quotientEvaluation_form (W : (threefold φ).Opens) (hW : WeightedBasis.Good φ W)
    (hw : KPoint.point g ∈ W) (a : (A φ 3).obj (op W)) :
    (eqToHom (if_pos hw) : (skyscraperSheaf (KPoint.point g) (rationalQuotient b)).obj.obj (op W) ⟶ _)
      ((quotientEvaluation φ g hg hp b x hx).hom.app (op W)
        ((toSheafify (BasisSheafification.J _) ((complex φ).X 3)).app (op W)
          ((fromForms φ 3).app (op W) a))) =
      (quotientMap b) (pull (KPoint.eval (toBase φ) g hg W hw) 3 a) := by
  have e := PointEvaluation.liftSky_app (atPoint φ g hg hp) (atPoint_d φ g hg hp b x hx) 3 W hw
  have h := ConcreteCategory.congr_hom e ((fromForms φ 3).app (op W) a)
  rw [atPoint_form φ g hg hp 3 W hW hw] at h
  change (eqToHom (if_pos hw) : _ ⟶ rationalQuotient b)
    (((SkyscraperPresheafFunctor.map' (KPoint.point g) (quotientMap b)).app (op W))
      (((evaluate φ g hg hp b x hx).f 3).hom.app (op W)
        ((toSheafify (BasisSheafification.J _) ((complex φ).X 3)).app (op W)
          ((fromForms φ 3).app (op W) a)))) = _
  change (eqToHom (if_pos hw) : _ ⟶ (fieldComplex b x hx).X 3)
    (((evaluate φ g hg hp b x hx).f 3).hom.app (op W)
      ((toSheafify (BasisSheafification.J _) ((complex φ).X 3)).app (op W)
        ((fromForms φ 3).app (op W) a))) = _ at h
  have es : ((SkyscraperPresheafFunctor.map' (KPoint.point g) (quotientMap b)).app (op W)) ≫
      eqToHom (if_pos hw) = eqToHom (if_pos hw) ≫ quotientMap b := by
    simp only [SkyscraperPresheafFunctor.map'_app, Opposite.unop_op, dif_pos hw,
      Category.assoc, eqToHom_trans, eqToHom_refl, Category.comp_id]
  exact (ConcreteCategory.congr_hom es _).trans (congrArg (quotientMap b) h)

end CycleQ2.Cech.WeightedFieldEvaluation
end
#print axioms CycleQ2.Cech.WeightedFieldEvaluation.quotientEvaluation_d
