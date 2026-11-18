import Proposal.GeometricLiteralMovingResidueAdjunction
import Proposal.GeometricAffinePairLifts

/-!
# Numerators of residue sections on affine opens

On an affine open equipped with a Cartier frame, every section of the
residue quotient is represented by a canonical numerator modulo the local
equation. Affine vanishing for the framed canonical sheaf lifts a residue
section to a pole, whose value on the ideal generator recovers its numerator.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingResidueAffineNumerators

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2SeedProjectiveImageCocycle (Surface)
open CycleQ2SeedSectionDivisorTransitions (FrameData)
open CycleQ2SeedSectionAffineInjective (ChartRegular)
open CycleQ2CanonicalResidueSheaf (CanonicalForms)
open CycleQ2LiteralMovingResiduePole (poleMap poleOfNumerator frame pole_ext_generator)
open CycleQ2LiteralMovingResidueExact (regularInclusion residueShortExact)
open CycleQ2LiteralMovingResidueAdjunction (numeratorToResidue numeratorToResidue_mk numeratorToResidue_injective)
open CycleQ2SurfaceCoordinateFrames (canonicalAdditiveSheaf coordinateCanonicalAdditiveFrame)
open CycleQ2GeometricProjectiveHOne (affineFrameHOne_subsingleton structureAdditiveSheaf overIsoOfPatchIso)

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0}) :=
  HasExt.standard _

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) {W : Surface.Opens} (j : FrameData W)

theorem poleMap_surjective : Function.Surjective (poleMap t ht j) := by
  intro H
  let V : Over W := Over.mk (𝟙 W)
  let j' := j.restrict (show W ≤ W from le_rfl)
  let σ := H.val.app (op V) (frame t ht j' 1)
  refine ⟨σ, pole_ext_generator t ht j' ?_⟩
  change (poleOfNumerator t ht j σ).val.app (op V) (frame t ht j' 1) = σ
  exact (CycleQ2LiteralMovingResiduePole.poleOfNumerator_app_frame t ht j σ V 1).trans
    ((one_smul Γ(Surface,W) (CanonicalForms.val.map (𝟙 (op W)) σ : CanonicalForms.val.obj (op W))).trans
      (ConcreteCategory.congr_hom (CanonicalForms.val.presheaf.map_id (op W)) σ))

include j in
theorem canonicalHOne_subsingleton (hW : IsAffineOpen W) :
    Subsingleton (canonicalAdditiveSheaf.H' 1 W) := by
  let e := coordinateCanonicalAdditiveFrame j.chart
  let f : CycleQ2GeometricSheafLocalIso.PatchIso canonicalAdditiveSheaf (structureAdditiveSheaf Surface) W :=
    { app := fun O hO => e.app O (hO.trans j.within)
      naturality := fun h hO s => e.naturality h (hO.trans j.within) s }
  exact affineFrameHOne_subsingleton hW.isoSpec canonicalAdditiveSheaf (overIsoOfPatchIso f)

theorem numeratorToResidue_surjective (hW : IsAffineOpen W) :
    Function.Surjective (numeratorToResidue t ht j) := by
  intro x
  obtain ⟨H, hH⟩ := CycleQ2CechTwoToDerived.sections_surjective_of_H_one_subsingleton
    (residueShortExact t ht) W (canonicalHOne_subsingleton j hW) x
  obtain ⟨σ, hσ⟩ := poleMap_surjective t ht j H
  refine ⟨_, (numeratorToResidue_mk t ht j σ).trans ?_⟩
  rw [hσ]
  exact hH

theorem numeratorToResidue_bijective (hW : IsAffineOpen W) :
    Function.Bijective (numeratorToResidue t ht j) :=
  ⟨numeratorToResidue_injective t ht j, numeratorToResidue_surjective t ht j hW⟩

end CycleQ2LiteralMovingResidueAffineNumerators
end

#print axioms CycleQ2LiteralMovingResidueAffineNumerators.numeratorToResidue_bijective
