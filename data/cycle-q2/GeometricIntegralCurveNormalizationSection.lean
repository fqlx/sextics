import Proposal.GeometricIntegralCurveNormalization
import Mathlib.AlgebraicGeometry.SpreadingOut

/-!
# Recovering a neighborhood of the generic point through the normalization

The section at the generic stalk spreads to an actual open of the curve.
Pullback by this section recovers the original family on that open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2IntegralCurveNormalization

open CategoryTheory AlgebraicGeometry TopologicalSpace CycleQ2GenericPointAffineSections

universe u
variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]
variable (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

include p in
/-- A section of the finite normalization exists on an open containing the
actual generic point of the original curve. -/
theorem dominant_section_over_generic_open : ∃ (U : X.Opens), genericPoint X ∈ U ∧
    ∃ σ : U.toScheme ⟶ Model X, IsDominant σ ∧ σ ≫ normalize X = U.ι := by
  have := finite k p
  have := residue_isIso X
  let φ := Spec.map (inv (X.residue (genericPoint X))) ≫ (point X).toNormalization
  have hφ : φ ≫ normalize X = X.fromSpecStalk (genericPoint X) ≫ 𝟙 X := by
    rw [Category.comp_id]
    change (_ ≫ (point X).toNormalization) ≫ (point X).fromNormalization = _
    rw [Category.assoc, Scheme.Hom.toNormalization_fromNormalization]
    change Spec.map (inv _) ≫ Spec.map (X.residue (genericPoint X)) ≫ X.fromSpecStalk _ = _
    rw [← Spec.map_comp_assoc, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]
  obtain ⟨U, hU, σ, hφσ, hσ⟩ := spread_out_of_isGermInjective' (𝟙 X) (normalize X) φ hφ
  have : IsDominant φ := by dsimp [φ]; infer_instance
  have : IsDominant (U.fromSpecStalkOfMem _ hU ≫ σ) := by rw [← hφσ]; infer_instance
  exact ⟨U, hU, σ, IsDominant.of_comp (U.fromSpecStalkOfMem _ hU) σ, hσ.trans (Category.comp_id _)⟩

include p in
theorem section_over_generic_open : ∃ (U : X.Opens), genericPoint X ∈ U ∧
    ∃ σ : U.toScheme ⟶ Model X, σ ≫ normalize X = U.ι := by
  obtain ⟨U, hU, σ, _, hσ⟩ := dominant_section_over_generic_open k p
  exact ⟨U, hU, σ, hσ⟩

private theorem restriction_iso_of_dominant_section {N Y : Scheme.{u}} [IsReduced N]
    (ν : N ⟶ Y) [IsSeparated ν] (U : Y.Opens) (σ : U.toScheme ⟶ N) [IsDominant σ]
    (hσ : σ ≫ ν = U.ι) : IsIso (ν ∣_ U) := by
  let h := isPullback_morphismRestrict ν U
  have w : 𝟙 _ ≫ U.ι = σ ≫ ν := by rw [Category.id_comp, hσ]
  let τ := h.lift (𝟙 _) σ w
  have hτ : τ ≫ (ν ∣_ U) = 𝟙 _ := h.lift_fst _ _ _
  have hτ' : τ ≫ (ν ⁻¹ᵁ U).ι = σ := h.lift_snd _ _ _
  have : IsDominant (τ ≫ (ν ⁻¹ᵁ U).ι) := by rw [hτ']; infer_instance
  have : IsDominant τ := IsDominant.of_comp_of_isOpenImmersion _ (ν ⁻¹ᵁ U).ι
  have : IsClosedImmersion (τ ≫ (ν ∣_ U)) := by rw [hτ]; infer_instance
  have : IsClosedImmersion τ := IsClosedImmersion.of_comp _ (ν ∣_ U)
  have : Surjective τ := surjective_of_isDominant_of_isClosed_range τ τ.isClosedEmbedding.isClosed_range
  have := isIso_of_isClosedImmersion_of_surjective τ
  exact IsIso.of_isIso_fac_left hτ

include p in
/-- The absolute normalization is an isomorphism above a neighborhood of the
generic point. The whole inverse image recovers the original open. -/
theorem iso_over_generic_open :
    ∃ U : X.Opens, genericPoint X ∈ U ∧ IsIso (normalize X ∣_ U) := by
  obtain ⟨U, hU, σ, hdom, hσ⟩ := dominant_section_over_generic_open k p
  have := finite k p
  exact ⟨U, hU, restriction_iso_of_dominant_section (normalize X) U σ hσ⟩

end CycleQ2IntegralCurveNormalization
end

#print axioms CycleQ2IntegralCurveNormalization.section_over_generic_open
#print axioms CycleQ2IntegralCurveNormalization.iso_over_generic_open
