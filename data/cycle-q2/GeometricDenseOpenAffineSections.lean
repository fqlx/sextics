import Mathlib.AlgebraicGeometry.Morphisms.UnderlyingMap
import Mathlib.AlgebraicGeometry.Morphisms.OpenImmersion
import Mathlib.AlgebraicGeometry.Morphisms.Finite

/-!
# Sections of a dense open on an affine chart

Intersecting a dense open subscheme with an affine chart gives a dense open
in the spectrum of the chart ring. The induced identification of sections
respects the original coordinate algebra.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2DenseOpenAffineSections
open CategoryTheory AlgebraicGeometry

variable {X Y : Scheme} (j : X ⟶ Y) [IsOpenImmersion j]
variable {V : Y.Opens} (hV : IsAffineOpen V)

def chart : (j ⁻¹ᵁ V).toScheme ⟶ Spec Γ(Y,V) := (j ∣_ V) ≫ hV.isoSpec.hom

instance : IsOpenImmersion (chart j hV) := by unfold chart; infer_instance

def chartOpen : (Spec Γ(Y,V)).Opens := chart j hV ''ᵁ ⊤

theorem dense [IsDominant j] : Dense (chartOpen j hV : Set (Spec Γ(Y, V))) := by
  let : IsDominant (j ∣_ V) := IsZariskiLocalAtTarget.restrict (P := @IsDominant) inferInstance V
  let : IsDominant (chart j hV) := by unfold chart; infer_instance
  rw [chartOpen, Scheme.Hom.image_top_eq_opensRange]
  exact (chart j hV).denseRange

def sectionIso : Γ(Spec Γ(Y,V), chartOpen j hV) ≅ Γ(X, j ⁻¹ᵁ V) :=
  ((chart j hV).appIso ⊤) ≪≫ (j ⁻¹ᵁ V).topIso

theorem sectionIso_over :
    CommRingCat.ofHom (algebraMap Γ(Y,V) Γ(Spec Γ(Y,V), chartOpen j hV)) ≫
      (sectionIso j hV).hom = j.app V := by
  let g := chart j hV
  have hle : g ''ᵁ ⊤ ≤ ⊤ := le_top
  have hres : (Spec Γ(Y,V)).presheaf.map (homOfLE hle).op ≫ (g.appIso ⊤).hom = g.appTop := by
    rw [g.appIso_hom', g.map_appLE (g.preimage_image_eq ⊤).ge (homOfLE hle).op]
    simp [Scheme.Hom.appLE]
    exact Category.comp_id g.appTop
  change ((Scheme.ΓSpecIso Γ(Y,V)).inv ≫ (Spec Γ(Y,V)).presheaf.map (homOfLE hle).op) ≫
    (sectionIso j hV).hom = j.app V
  rw [sectionIso, Iso.trans_hom]
  rw [Category.assoc, ← Category.assoc _ (g.appIso ⊤).hom, hres]
  dsimp only [g, chart]
  rw [Scheme.Hom.comp_appTop, hV.isoSpec_hom_appTop, morphismRestrict_appTop]
  simp [Scheme.Opens.topIso_hom, Scheme.Opens.topIso_inv, Scheme.Hom.app_eq_appLE]

/-- Actual section algebra on the restricted open, in chart coordinates. -/
def sectionEquiv :
    letI := (j.app V).hom.toAlgebra
    Γ(X, j ⁻¹ᵁ V) ≃ₐ[Γ(Y,V)] Γ(Spec Γ(Y,V), chartOpen j hV) := by
  letI := (j.app V).hom.toAlgebra
  let e := (sectionIso j hV).symm.commRingCatIsoToRingEquiv
  refine AlgEquiv.ofRingEquiv (f := e) ?_
  intro r
  apply (sectionIso j hV).commRingCatIsoToRingEquiv.injective
  exact (e.symm_apply_apply _).trans (ConcreteCategory.congr_hom (sectionIso_over j hV) r).symm

end CycleQ2DenseOpenAffineSections

#print axioms CycleQ2DenseOpenAffineSections.dense
#print axioms CycleQ2DenseOpenAffineSections.sectionEquiv
