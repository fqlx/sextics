import Proposal.GeometricLiteralIncidenceGenericModel
import Proposal.GeometricIncidenceIntegralComponent
import Proposal.GeometricIntegralCurveNormalizationSection

/-!
# A proper smooth generic curve retaining a prescribed time test

Take the schematic closure of an irreducible open of the generic time fiber
inside the proper fiber and normalize in its function field. A dense open of the
resulting smooth proper integral curve comes from the original test through the
original time and fiber maps.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralIncidenceGenericSmoothCurve

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  CycleQ2IncidenceEtaleParameter CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2LiteralIncidenceNormalizedSlice CycleQ2LiteralIncidenceGenericModel

variable (V : parameterScheme.Opens)

abbrev testMap : TimeFiber V ⟶ Time toRaw V :=
  pullback.snd _ (CycleQ2LiteralIncidenceRelativeNormalization.openInclusion V)

private theorem recover_open {T X : Scheme} [IsIntegral X] (p : X ⟶ Spec (CommRingCat.of K))
    [LocallyOfFiniteType p] (a : T ⟶ X) [IsOpenImmersion a] [IsDominant a] :
    ∃ D : T.Opens, (D : Set T).Nonempty ∧
      ∃ d : D.toScheme ⟶ CycleQ2IntegralCurveNormalization.Model X,
        IsOpenImmersion d ∧ IsDominant d ∧
        d ≫ CycleQ2IntegralCurveNormalization.normalize X = D.ι ≫ a := by
  let n := CycleQ2IntegralCurveNormalization.normalize X
  obtain ⟨G, hG, hi⟩ := CycleQ2IntegralCurveNormalization.iso_over_generic_open K p
  let D := a ⁻¹ᵁ G
  have hD : (D : Set T).Nonempty := a.denseRange.exists_mem_open G.isOpen ⟨_, hG⟩
  let d := (a ∣_ G) ≫ inv (n ∣_ G) ≫ (n ⁻¹ᵁ G).ι
  have : IsOpenImmersion d := by dsimp only [d]; infer_instance
  have : Nonempty D.toScheme := hD.to_subtype
  have hd : IsDominant d := ⟨IsOpenMap.denseRange_of_isPreirreducibleSpace _ d.isOpenMap⟩
  refine ⟨D, hD, d, inferInstance, hd, ?_⟩
  simp only [d, Category.assoc, ← morphismRestrict_ι, IsIso.inv_hom_id_assoc]

private instance time_noetherian : NoetherianSpace (TimeFiber V) := by
  have : NoetherianSpace (Fiber V) := noetherian_of_proper (projection V)
  exact (inclusion V).isOpenEmbedding.isInducing.noetherianSpace

/-- The smooth proper generic curve contains a dense open from the original test.
The maps to the compactified fiber and to the test agree with the given projections. -/
theorem test_proper_smooth_curve (W : (Time toRaw V).Opens) (hW : (W : Set (Time toRaw V)).Nonempty) :
    ∃ (U : (TimeFiber V).Opens) (hle : U ≤ (testMap V) ⁻¹ᵁ W), IsIntegral U.toScheme ∧
      ∃ hI : IsIntegral (CycleQ2IncidenceIntegralComponent.Model (inclusion V) U),
        let C := @CycleQ2IntegralCurveNormalization.Model _ hI
        let n := @CycleQ2IntegralCurveNormalization.normalize _ hI
        let p := CycleQ2IncidenceIntegralComponent.toBase (inclusion V) (projection V) U
        IsIntegral C ∧ IsFinite n ∧ IsProper (n ≫ p) ∧ Smooth (n ≫ p) ∧ Surjective (n ≫ p) ∧
        (∀ A : C.affineOpens, Ring.KrullDimLE 1 Γ(C, A.1)) ∧
        ∃ D : U.toScheme.Opens, (D : Set U.toScheme).Nonempty ∧
          ∃ d : D.toScheme ⟶ C, IsOpenImmersion d ∧ IsDominant d ∧
            SmoothOfRelativeDimension 1 (d ≫ n ≫ p) ∧
            d ≫ n = D.ι ≫ CycleQ2IncidenceIntegralComponent.openInclusion (inclusion V) U ∧
            d ≫ n ≫ (U.ι ≫ inclusion V).imageι = D.ι ≫ U.ι ≫ inclusion V ∧
            (D.ι ≫ (testMap V).resLE W U hle) ≫ W.ι = D.ι ≫ U.ι ≫ testMap V ∧
            ∃ O : C.Opens, Dense (O : Set C) ∧
              ∃ e : D.toScheme ≅ O.toScheme, e.hom ≫ O.ι = d := by
  obtain ⟨x, hx⟩ := test_meets_generic V W hW
  obtain ⟨U, hle, hU, hI, hs, _, _⟩ :=
    CycleQ2IncidenceIntegralComponent.exists_model (inclusion V) (projection V)
      ((testMap V) ⁻¹ᵁ W) ⟨x, hx⟩
  let Y := CycleQ2IncidenceIntegralComponent.Model (inclusion V) U
  let p := CycleQ2IncidenceIntegralComponent.toBase (inclusion V) (projection V) U
  let a := CycleQ2IncidenceIntegralComponent.openInclusion (inclusion V) U
  let n := CycleQ2IntegralCurveNormalization.normalize Y
  have : IsFinite n := CycleQ2IntegralCurveNormalization.finite K p
  have : NoetherianSpace U.toScheme := NoetherianSpace.set (U : Set (TimeFiber V))
  have hdY (A : Y.affineOpens) : Ring.KrullDimLE 1 Γ(Y,A.1) :=
    CycleQ2CurveChartDimension.chart_dimension a p A.2
  have hp := CycleQ2IntegralCurveNormalization.proper K p
  have hsm := CycleQ2IntegralCurveNormalization.smooth_of_affine_dimension K p hdY
  have hsur : Surjective (n ≫ p) :=
    ⟨fun z => ⟨Classical.choice (inferInstance : Nonempty (CycleQ2IntegralCurveNormalization.Model Y)),
      Subsingleton.elim _ z⟩⟩
  obtain ⟨D, hD, d, hdo, hdd, hdn⟩ := recover_open p a
  have : NoetherianSpace D.toScheme := NoetherianSpace.set (D : Set U.toScheme)
  have hdsm : SmoothOfRelativeDimension 1 (d ≫ n ≫ p) := by
    rw [← Category.assoc, hdn, Category.assoc]
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 1 D.ι (a ≫ p)
  refine ⟨U, hle, hU, hI, inferInstance, inferInstance, hp, hsm, hsur, fun A =>
    CycleQ2CurveChartDimension.chart_dimension d (n ≫ p) A.2, D, hD, d, hdo, hdd, hdsm, hdn, ?_, ?_, ?_⟩
  · rw [← Category.assoc, hdn, Category.assoc]
    simp [a, CycleQ2IncidenceIntegralComponent.openInclusion]
  · rw [Category.assoc, Scheme.Hom.resLE_comp_ι]
  · exact ⟨d.opensRange, d.denseRange, d.isoOpensRange, d.isoOpensRange_hom_ι⟩

end CycleQ2LiteralIncidenceGenericSmoothCurve
end

#print axioms CycleQ2LiteralIncidenceGenericSmoothCurve.test_proper_smooth_curve
