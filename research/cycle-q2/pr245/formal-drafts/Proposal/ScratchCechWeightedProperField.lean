import Proposal.ScratchCechWeightedProper
import Proposal.ScratchCechWeightedFieldEvaluation
import Proposal.ScratchDerivedResidueLocalPrimitive

/-! Vanishing of the proper degree-three class produces an ordinary rational
two-form primitive of the evaluated vertex at any field-valued point. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section
open AlgebraicGeometry CategoryTheory Opposite
open CycleQ2WeightedResidueAtlas CycleQ2GeometricHodgeThreefold CycleQ2GenericSexticGradient
open CycleQ2WeightedNativeCech (double)
open CycleQ2LogarithmicDifferential (exteriorD)
open CycleQ2LogarithmicChartDerivative (pull)

namespace CycleQ2.Cech.WeightedSheaf

variable {k L : Type} [CommRing k] [Field L] [Algebra k L] (φ : CoeffRing →+* k)
  [HasDerivedCategory (CycleQ2InjectiveCech.AbSheaf (threefold φ : TopCat))]
  (g : Spec (CommRingCat.of L) ⟶ threefold φ)
  (hg : g ≫ toBase φ = Spec.map (CommRingCat.ofHom (algebraMap k L)))
  (hp : IsUnit (φ goodParameter))
  {I : Type} [LinearOrder I] [Fintype I] (e : Module.Basis I L (KaehlerDifferential k L))
  (x : I → L) (hx : ∀ j, e j = KaehlerDifferential.D k L (x j))
  (a : (double φ).X 0 3) (b : (double φ).X 1 2) (c : (double φ).X 2 1)
  (ha : (double φ).v 0 3 a = 0) (hb : (double φ).h 0 3 a = -((double φ).v 1 2 b))
  (hc : (double φ).h 1 2 b = (double φ).v 2 1 c) (hd : (double φ).h 2 1 c = 0)

/-- Detect exactness of a single chart form using its rational quotient
at the field-valued point. -/
theorem primitive_of_quotient_zero (i : Index) (hi : KPoint.point g ∈ U φ i)
    (ω : (WeightedGoodComplex.A φ 3).obj (op (U φ i)))
    (h : (WeightedFieldEvaluation.quotientEvaluation φ g hg hp e x hx).hom.app (op (U φ i))
      ((toGlobal φ 3).app (op (U φ i)) ω) = 0) :
    ∃ η : CycleQ2LogarithmicPullback.Forms k L 2, exteriorD e 2 η =
      pull (KPoint.eval (toBase φ) g hg (U φ i) hi) 3 ω := by
  have hq := WeightedFieldEvaluation.quotientEvaluation_form φ g hg hp e x hx
    (U φ i) (WeightedBasis.good_vertex φ i) hi ω
  change (eqToHom _ : _ ⟶ WeightedFieldEvaluation.rationalQuotient e)
    ((WeightedFieldEvaluation.quotientEvaluation φ g hg hp e x hx).hom.app (op (U φ i))
       ((toGlobal φ 3).app (op (U φ i)) ω)) = _ at hq
  rw [h,map_zero] at hq
  exact (QuotientAddGroup.eq_zero_iff _).mp hq.symm

/-- After restriction to a field-valued point on the specified chart, the
proper-class vanishing gives a two-form primitive with no loss of coefficients. -/
theorem fieldPrimitive (hzero : properClass φ a b c ha hb hc hd hp = 0)
    (i : Index) (hi : KPoint.point g ∈ U φ i) :
    ∃ η : CycleQ2LogarithmicPullback.Forms k L 2, exteriorD e 2 η =
      pull (KPoint.eval (toBase φ) g hg (U φ i) hi) 3
        (vertex (U φ) (WeightedGoodComplex.A φ 3) i a) := by
  apply primitive_of_quotient_zero φ g hg hp e x hx i hi
  have h := GlobalResidueClass.annihilator_of_properClassNat_zero (U := U φ) (K φ) (cover φ hp)
    (sheafResidues φ a b c ha hb hc hd) hzero i
    (WeightedFieldEvaluation.quotientEvaluation φ g hg hp e x hx)
    (WeightedFieldEvaluation.quotientEvaluation_d φ g hg hp e x hx)
  rwa [sheafResidues_vertex] at h

/-- A restriction into a second neighborhood of the same point acts by
the identity on the skyscraper value, and so detects zero sections. -/
theorem sky_restrict_injective {Y : TopCat} (p : Y)
    [∀ W : TopologicalSpace.Opens Y, Decidable (p ∈ W)] (Q : AddCommGrpCat.{0})
    {V W : TopologicalSpace.Opens Y} (h : V ≤ W) (hv : p ∈ V) :
    Function.Injective ((skyscraperSheaf p Q).obj.map (homOfLE h).op) := by
  change Function.Injective ((skyscraperPresheaf p Q).map (homOfLE h).op)
  rw [skyscraperPresheaf_map,dif_pos hv]
  exact (ConcreteCategory.bijective_of_isIso _).injective

/-- The class of a chart form modulo exact rational forms only depends
on its restriction to any neighborhood containing the field-valued point. -/
theorem primitive_of_neighborhood_quotient_zero (i : Index) (hi : KPoint.point g ∈ U φ i)
    (ω : (WeightedGoodComplex.A φ 3).obj (op (U φ i)))
    (V : (threefold φ).Opens) (hVi : V ≤ U φ i) (hv : KPoint.point g ∈ V)
    (h : (WeightedFieldEvaluation.quotientEvaluation φ g hg hp e x hx).hom.app (op V)
      (((K φ).X 3).obj.map (homOfLE hVi).op ((toGlobal φ 3).app (op (U φ i)) ω)) = 0) :
    ∃ η : CycleQ2LogarithmicPullback.Forms k L 2, exteriorD e 2 η =
      pull (KPoint.eval (toBase φ) g hg (U φ i) hi) 3 ω := by
  classical
  apply primitive_of_quotient_zero φ g hg hp e x hx i hi
  apply sky_restrict_injective (KPoint.point g) (WeightedFieldEvaluation.rationalQuotient e) hVi hv
  rw [map_zero]
  exact (NatTrans.naturality_apply
    (WeightedFieldEvaluation.quotientEvaluation φ g hg hp e x hx).hom
    (homOfLE hVi).op ((toGlobal φ 3).app (op (U φ i)) ω)).symm.trans h

/-- It suffices that the proper class vanish after restriction to an open
containing the point of evaluation. -/
theorem fieldPrimitive_of_restrict_zero (W : (threefold φ).Opens) (hw : KPoint.point g ∈ W)
    (hzero : DerivedCategory.Q.map
      ((HomologicalComplex.single (CycleQ2InjectiveCech.AbSheaf (threefold φ : TopCat))
        (ComplexShape.up ℤ) (3 : ℤ)).map
        (CycleQ2InjectiveCech.freeOpenMap (show W ≤ ⊤ from le_top))) ≫
        properClass φ a b c ha hb hc hd hp = 0)
    (i : Index) (hi : KPoint.point g ∈ U φ i) :
    ∃ η : CycleQ2LogarithmicPullback.Forms k L 2, exteriorD e 2 η =
      pull (KPoint.eval (toBase φ) g hg (U φ i) hi) 3
        (vertex (U φ) (WeightedGoodComplex.A φ 3) i a) := by
  apply primitive_of_neighborhood_quotient_zero φ g hg hp e x hx i hi _
    (U φ i ⊓ W) inf_le_left ⟨hi,hw⟩
  have h := GlobalResidueClass.annihilator_of_properClassNat_restrict_zero (U := U φ) (K φ)
    (cover φ hp) (sheafResidues φ a b c ha hb hc hd) W hzero i (U φ i ⊓ W) le_rfl
    (WeightedFieldEvaluation.quotientEvaluation φ g hg hp e x hx)
    (WeightedFieldEvaluation.quotientEvaluation_d φ g hg hp e x hx)
  rwa [sheafResidues_vertex] at h

end CycleQ2.Cech.WeightedSheaf
end

#print axioms CycleQ2.Cech.WeightedSheaf.fieldPrimitive
#print axioms CycleQ2.Cech.WeightedSheaf.fieldPrimitive_of_restrict_zero
