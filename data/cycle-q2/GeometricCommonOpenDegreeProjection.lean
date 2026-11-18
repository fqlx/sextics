import Proposal.GeometricLiteralCanonicalDegreeProjection
import Proposal.GeometricFamilyDeformation

/-!
# Degree-zero projection on a common projective open

An algebra map between the ordinary localizations at two homogeneous
denominators preserves the associated projective function on their
common open after taking degree zero. The proof compares both
denominators with their product, so no particular denominator
factorization or positive degree is required.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2CommonOpenDegreeProjection
open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2GradedLocalizationProjection CycleQ2GeometricKernelLocalization

variable {A σ : Type*} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
variable (𝒜 : ℕ → σ) [GradedRing 𝒜]

private def section {f : A} {d : ℕ} (hf : f ∈ 𝒜 d) (W : (Proj 𝒜).Opens)
    (hW : W ≤ Proj.basicOpen 𝒜 f) (z : Localization.Away f) : Γ(Proj 𝒜,W) :=
  (Proj 𝒜).presheaf.map (homOfLE hW).op ((Proj.awayToSection 𝒜 f).hom (degreeZero 𝒜 hf z))

private theorem factor {f g x : A} {d e dx : ℕ} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (hx : x = f * g) (hxhom : x ∈ 𝒜 dx) (ρ : Localization.Away f →ₐ[A] Localization.Away x)
    (W : (Proj 𝒜).Opens) (hW : W ≤ Proj.basicOpen 𝒜 x) (z : Localization.Away f) :
    section 𝒜 hxhom W hW (ρ z) = section 𝒜 hf W (hW.trans (Proj.basicOpen_mono _ _ _ ⟨g,hx⟩)) z := by
  unfold section
  rw [degreeZero_naturality 𝒜 hf hg hx hxhom ρ]
  have h := ConcreteCategory.congr_hom (Proj.awayMap_awayToSection 𝒜 hg hx) (degreeZero 𝒜 hf z)
  change (Proj.awayToSection 𝒜 x).hom _ =
    (Proj 𝒜).presheaf.map _ ((Proj.awayToSection 𝒜 f).hom _) at h
  rw [h]
  exact (ConcreteCategory.congr_hom ((Proj 𝒜).presheaf.map_comp _ _) _).symm

theorem commonOpen {f g : A} {d e : ℕ} (hf : f ∈ 𝒜 d) (hg : g ∈ 𝒜 e)
    (ρ : Localization.Away f →ₐ[A] Localization.Away g)
    (W : (Proj 𝒜).Opens) (hWf : W ≤ Proj.basicOpen 𝒜 f) (hWg : W ≤ Proj.basicOpen 𝒜 g)
    (z : Localization.Away f) :
    (Proj 𝒜).presheaf.map (homOfLE hWg).op ((Proj.awayToSection 𝒜 g).hom (degreeZero 𝒜 hg (ρ z))) =
      (Proj 𝒜).presheaf.map (homOfLE hWf).op ((Proj.awayToSection 𝒜 f).hom (degreeZero 𝒜 hf z)) := by
  let x := f * g
  have hx : x ∈ 𝒜 (d+e) := SetLike.mul_mem_graded hf hg
  let F : Localization.Away f →ₐ[A] Localization.Away x := thickRestriction A (dvd_mul_right f g)
  let G : Localization.Away g →ₐ[A] Localization.Away x := thickRestriction A (dvd_mul_left g f)
  have H : G.comp ρ = F := by
    apply AlgHom.coe_ringHom_injective
    apply IsLocalization.ringHom_ext (Submonoid.powers f)
    apply RingHom.ext
    intro a
    exact ((G.comp ρ).commutes a).trans (F.commutes a).symm
  have hWx : W ≤ Proj.basicOpen 𝒜 x := by
    rw [show x = f * g from rfl, Proj.basicOpen_mul]
    exact le_inf hWf hWg
  have hG := factor 𝒜 hg hf (show x = g * f from mul_comm f g) hx G W hWx (ρ z)
  have hF := factor 𝒜 hf hg (show x = f * g from rfl) hx F W hWx z
  exact hG.symm.trans ((congrArg (section 𝒜 hx W hWx) (AlgHom.congr_fun H z)).trans hF)

end CycleQ2CommonOpenDegreeProjection
end

#print axioms CycleQ2CommonOpenDegreeProjection.commonOpen
