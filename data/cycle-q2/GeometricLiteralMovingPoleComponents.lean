import Proposal.GeometricClosedComponentsCohomology
import Proposal.GeometricDisjointClosedSheafDecomposition
import Proposal.GeometricLiteralMovingPoleComponentsDisjoint
import Proposal.GeometricLiteralMovingPoleAffineComponents

/-!
# The positive pole quotient splits along the three translated curves

On an affine neighbourhood missing all three curves the pivot ideal is the
unit ideal, so the pole quotient has zero stalk. Its three actual
closed-image restrictions therefore give a product decomposition on the
literal surface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralMovingPoleComponents

open CategoryTheory CategoryTheory.Limits TopologicalSpace TopCat.Presheaf
  Opposite AlgebraicGeometry CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedSectionAffineInjective CycleQ2SeedSectionDivisorTransitions
  CycleQ2SeedSectionSheafGlobal CycleQ2LiteralMovingResidueBasis
  CycleQ2LiteralMovingPoleQuotient CycleQ2LiteralOrbitAction
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralNativeCartierFrames CycleQ2LiteralMovingDivisorOrbitFrames
  CycleQ2LinkageComponentDecomposition CycleQ2LinkageComponentAlgebra
  CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2CartierSurfaceGrading
  CycleQ2SeedCyclicAction

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

/-- The original pole quotient has zero stalk away from all three images. -/
theorem pole_stalk_off_range (x : Surface) (hx : ∀ a, x ∉ Set.range (curveComponent a).base) :
    Subsingleton (stalk (C := AddCommGrpCat) (poleQuotient t ht).obj x) := by
  let U : Surface.Opens := ⟨(⋃ a, Set.range (curveComponent a).base)ᶜ,
    (isClosed_iUnion_of_finite (fun a => (curveComponent a).isClosedEmbedding.isClosed_range)).isOpen_compl⟩
  have hxU : x ∈ U := fun h => by
    obtain ⟨a,ha⟩ := Set.mem_iUnion.mp h
    exact hx a ha
  let F := poleQuotient t ht
  have hzero (b : stalk (C := AddCommGrpCat) F.obj x) : b = 0 := by
    obtain ⟨V,hxV,s,rfl⟩ := exists_germ_eq F.obj b
    obtain ⟨W,v,hxW,hW,hv⟩ := exists_componentNeighborhood (show x ∈ V ⊓ U from ⟨hxV,hxU⟩)
    have hV : W.carrier ≤ V := hW.trans inf_le_left
    have hempty (a : Fin 3) : (curveComponent a) ⁻¹ᵁ W.carrier = ⊥ := by
      apply le_antisymm _ bot_le
      intro c hc
      exact ((hW hc).2 (Set.mem_iUnion.mpr ⟨a,c,rfl⟩)).elim
    letI := quotient_sections_off t ht W v hv hempty
    have hz : F.obj.map (homOfLE hV).op s = 0 := Subsingleton.elim _ _
    rw [← germ_res_apply F.obj (homOfLE hV) x hxW, hz, map_zero]
  exact ⟨fun b c => (hzero b).trans (hzero c).symm⟩

/-- The projections are the canonical sheaf restrictions to the three translated curves. -/
def poleComponentsIso : poleQuotient t ht ≅ ∏ᶜ (fun a =>
    CycleQ2DisjointClosedSheafDecomposition.component (fun i => (curveComponent i).base)
      (poleQuotient t ht) a) :=
  CycleQ2DisjointClosedSheafDecomposition.decomposition (fun a => (curveComponent a).base)
    (fun a => (curveComponent a).isClosedEmbedding) _ components_pairwiseDisjoint
    (pole_stalk_off_range t ht)

local instance (X : Scheme.{0}) : CategoryTheory.HasExt.{1}
    (CategoryTheory.Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) :=
  CategoryTheory.HasExt.standard _
local instance (X : TopCat.{0}) : CategoryTheory.HasExt.{1} (CycleQ2InjectiveCech.AbSheaf X) :=
  CategoryTheory.HasExt.standard _
local instance (X : TopCat.{0}) : CategoryTheory.HasExt.{1} (X.Sheaf AddCommGrpCat.{0}) :=
  CategoryTheory.HasExt.standard _

/-- Vanishing on the three curves implies vanishing for the actual pole quotient. -/
theorem poleQuotient_HOne_of_component
    (h : ∀ a, Subsingleton ((CycleQ2ClosedSupportedRestriction.inverseSheaf (curveComponent a).base
      (poleQuotient t ht)).H' 1 ⊤)) : Subsingleton ((poleQuotient t ht).H' 1 ⊤) := by
  let e := CycleQ2ClosedComponentsCohomology.componentHEquiv (fun a => (curveComponent a).base)
    (fun a => (curveComponent a).isClosedEmbedding)
    (fun a => CycleQ2ClosedSupportedRestriction.inverseSheaf (curveComponent a).base (poleQuotient t ht))
    (poleComponentsIso t ht) 1
  exact ⟨fun x y => e.injective (funext fun a => (h a).elim _ _)⟩

end CycleQ2LiteralMovingPoleComponents
end

#print axioms CycleQ2LiteralMovingPoleComponents.poleComponentsIso
#print axioms CycleQ2LiteralMovingPoleComponents.poleQuotient_HOne_of_component
