import Proposal.GeometricClosedEmbeddingSheafExact
import Proposal.GeometricLiteralMovingPoleAffineComponents
import Proposal.GeometricLiteralMovingPoleComponentGluing

/-!
# Comparing the positive pole quotient using curve coefficients

A frame of each component sheaf on its single-component neighborhoods gives
a global comparison when its coefficients have the seventh-twist and orbit
transition of the pole quotient. Both sheaves have zero coefficients on
the other components of such a neighborhood.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralMovingPoleCoefficientGluing

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
  CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionAffineInjective
  CycleQ2SeedSectionDivisorTransitions CycleQ2LiteralMovingPoleComponents
  CycleQ2LiteralMovingPoleQuotient CycleQ2GeometricProjectiveCurve
  CycleQ2ClosedEmbeddingSheafExact

abbrev C := projectiveCurve 57 1
abbrev CurveSheaf := TopCat.Sheaf AddCommGrpCat.{0} (show TopCat from C)
abbrev factor (G : Fin 3 → CurveSheaf) (a : Fin 3) := (push (curveComponent a).base).obj (G a)
abbrev curveRing (W : ComponentPatch) (a : Fin 3) := Γ(C,(curveComponent a) ⁻¹ᵁ W.carrier)

def gauge (W V : ComponentPatch) (h : V.carrier ≤ W.carrier) : Γ(Surface,V.carrier) :=
  (transitionUnit W.frame.chart V.frame.chart V.carrier (h.trans W.frame.within) V.frame.within :
    Γ(Surface,V.carrier)) ^ 7 * (orbitTransition (W.frame.restrict h) V.frame : Γ(Surface,V.carrier))

/-- Coordinates on the component that a patch can meet, with their restriction law. -/
structure ComponentCoefficients (G : Fin 3 → CurveSheaf) where
  equiv (W : ComponentPatch) (a : Fin 3) (hs : W.survivor = some a) :
    (factor G a).obj.obj (op W.carrier) ≃+ curveRing W a
  restrict (W V : ComponentPatch) (a : Fin 3) (hw : W.survivor = some a)
      (hv : V.survivor = some a) (h : V.carrier ≤ W.carrier) (s : (factor G a).obj.obj (op W.carrier)) :
    equiv V a hv ((factor G a).obj.map (homOfLE h).op s) =
      (curveComponent a).app V.carrier (gauge W V h) *
        C.presheaf.map (homOfLE ((curveComponent a).preimage_mono h)).op (equiv W a hw s)

variable {G : Fin 3 → CurveSheaf} (d : ComponentCoefficients G)
  (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

private theorem ring_off (W : ComponentPatch) (a : Fin 3) (he : (curveComponent a) ⁻¹ᵁ W.carrier = ⊥) :
    Subsingleton (curveRing W a) := by
  change Subsingleton Γ(C,(curveComponent a) ⁻¹ᵁ W.carrier)
  rw [he]
  infer_instance

private def patchFactor (W : ComponentPatch) (a : Fin 3) :
    (factor G a).obj.obj (op W.carrier) ≃+ curveRing W a := by
  classical
  by_cases hs : W.survivor = some a
  · exact d.equiv W a hs
  · have he := W.avoids a hs
    have htgt := ring_off W a he
    have hsrc : Subsingleton ((factor G a).obj.obj (op W.carrier)) :=
      AddCommGrpCat.isZero_iff_subsingleton.mp ((G a).isTerminalOfEqEmpty he).isZero
    exact AddEquiv.ofBijective (0 : (factor G a).obj.obj (op W.carrier) →+ curveRing W a)
      ⟨fun _ _ _ => hsrc.elim _ _, fun b => ⟨0, htgt.elim _ b⟩⟩

private theorem patchFactor_survivor (W : ComponentPatch) (a : Fin 3) (hs : W.survivor = some a) :
    patchFactor d W a = d.equiv W a hs := by
  classical
  simp [patchFactor, hs]

private def targetCoordinates (W : ComponentPatch) :
    (∏ᶜ factor G).obj.obj (op W.carrier) ≃+ (∀ a, curveRing W a) :=
  (productSectionsEquiv (factor G) W.carrier).trans (AddEquiv.piCongrRight (patchFactor d W))

private def patchComparison (W : ComponentPatch) :
    (poleQuotient t ht).obj.obj (op W.carrier) ≃+ (∏ᶜ factor G).obj.obj (op W.carrier) :=
  (poleAffineComponents t ht W.toFramedAffine W.vertices W.within).trans (targetCoordinates d W).symm

private theorem comparison_coefficient (W : ComponentPatch)
    (s : (poleQuotient t ht).obj.obj (op W.carrier)) (a : Fin 3) :
    targetCoordinates d W (patchComparison d t ht W s) a =
      poleAffineComponents t ht W.toFramedAffine W.vertices W.within s a :=
  congrFun ((targetCoordinates d W).apply_symm_apply _) a

private theorem target_restrict (W V : ComponentPatch) (a : Fin 3) (hw : W.survivor = some a)
    (hv : V.survivor = some a) (h : V.carrier ≤ W.carrier) (s : (∏ᶜ factor G).obj.obj (op W.carrier)) :
    targetCoordinates d V ((∏ᶜ factor G).obj.map (homOfLE h).op s) a =
      (curveComponent a).app V.carrier (gauge W V h) *
        C.presheaf.map (homOfLE ((curveComponent a).preimage_mono h)).op (targetCoordinates d W s a) := by
  change patchFactor d V a (productSectionsEquiv _ _ _ a) =
    _ * C.presheaf.map _ (patchFactor d W a (productSectionsEquiv _ _ _ a))
  rw [productSectionsEquiv_restrict, patchFactor_survivor d W a hw, patchFactor_survivor d V a hv]
  exact d.restrict W V a hw hv h _

/-- The affine CRT and these local component frames identify the actual pole quotient
    with the product of the direct images of the original component sheaves. -/
def poleCoefficientGluingIso : poleQuotient t ht ≅ ∏ᶜ factor G := by
  apply componentBasisIso (patchComparison d t ht)
  apply compatible_of_same_survivor
  · intro V hv
    exact ⟨fun x y => (targetCoordinates d V).injective (funext fun a => (ring_off V a (hv a)).elim _ _)⟩
  · intro W V h hs x
    apply (targetCoordinates d V).injective
    funext a
    by_cases hv : V.survivor = some a
    · rw [comparison_coefficient, target_restrict d W V a (hs.trans hv) hv h, comparison_coefficient]
      exact poleAffineComponents_restrict t ht W.toFramedAffine W.vertices W.within
        V.toFramedAffine V.vertices V.within h x a
    · exact (ring_off V a (V.avoids a hv)).elim _ _

end CycleQ2LiteralMovingPoleCoefficientGluing
end

#print axioms CycleQ2LiteralMovingPoleCoefficientGluing.poleCoefficientGluingIso
