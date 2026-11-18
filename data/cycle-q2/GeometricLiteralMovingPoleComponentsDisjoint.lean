import Proposal.GeometricLiteralMovingPoleComponentsCRT
import Proposal.GeometricLiteralMovingPoleComponentsImmersion
import Proposal.GeometricLiteralMovingResidueBasis

/-!
# Disjointness of the three translated curves in the surface

Around each point a single affine neighborhood trivializes all three
Cartier frames. A point belonging to two translated curves would give
a proper prime ideal containing both of their comaximal defining ideals.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingPoleComponents

open CategoryTheory AlgebraicGeometry TopologicalSpace
  CycleQ2LinkageComponentDecomposition CycleQ2LinkageComponentAlgebra
  CycleQ2SeedProjectiveImageCocycle CycleQ2LiteralMovingResidueBasis
  CycleQ2LiteralOrbitAction CycleQ2LiteralOrbitChern CycleQ2LiteralNativeGaugeSections
  CycleQ2LiteralProjectiveIntersections

abbrev curveComponent (a : Fin 3) := componentImmersion (rootValues complexRoot a)
  (rootValues_cube complexRoot complexRoot_quadratic a)

private abbrev action (a : Fin 3) := (closedProjectiveAction (rootValues complexRoot a)
  (rootValues_cube complexRoot complexRoot_quadratic a)).hom

/-- Common affine neighborhoods simultaneously subordinate to all three
pulled-back native Cartier covers are cofinal at every point. -/
theorem exists_componentNeighborhood {x : Surface} {U : Surface.Opens} (hx : x ∈ U) :
    ∃ (W : FramedAffine) (v : Fin 3 → Vertex), x ∈ W.carrier ∧ W.carrier ≤ U ∧
      ∀ a, W.carrier ≤ (closedProjectiveAction (rootValues complexRoot a)
        (rootValues_cube complexRoot complexRoot_quadratic a)).hom ⁻¹ᵁ cover (v a) := by
  have hv (a : Fin 3) : ∃ v : Vertex, x ∈ translatedCover (action a) v := by
    apply Opens.mem_iSup.mp
    rw [translatedCover_top]
    trivial
  choose v hv using hv
  let O (a : Fin 3) := translatedCover (action a) (v a)
  let T := U ⊓ O 0 ⊓ O 1 ⊓ O 2
  have hxT : x ∈ T := ⟨⟨⟨hx,hv 0⟩,hv 1⟩,hv 2⟩
  obtain ⟨_,⟨W,rfl⟩,hxW,hWT⟩ := Opens.isBasis_iff_nbhd.mp isBasis_framedAffine hxT
  refine ⟨W,v,hxW,hWT.trans ((inf_le_left.trans inf_le_left).trans inf_le_left),?_⟩
  intro a
  fin_cases a
  · exact hWT.trans ((inf_le_left.trans inf_le_left).trans inf_le_right)
  · exact hWT.trans (inf_le_left.trans inf_le_right)
  · exact hWT.trans inf_le_right

/-- On an affine open the prime of any image point contains the ring kernel
of the corresponding closed immersion. -/
theorem ker_le_primeIdealOf_range {X Y : Scheme.{0}} (j : X ⟶ Y) [IsClosedImmersion j]
    {U : Y.Opens} (hU : IsAffineOpen U) {y : Y} (hy : y ∈ U) (hj : y ∈ Set.range j.base) :
    RingHom.ker (j.app U).hom ≤ (hU.primeIdealOf ⟨y,hy⟩).asIdeal := by
  obtain ⟨x,rfl⟩ := hj
  let V := j ⁻¹ᵁ U
  have hV : IsAffineOpen V := hU.preimage j
  have he := IsAffineOpen.comap_primeIdealOf_appLE (f := j) (x := x) U hU V hV le_rfl hy
  rw [← he]
  intro r hr
  change j.appLE U V le_rfl r ∈ (hV.primeIdealOf ⟨x,hy⟩).asIdeal
  rw [Scheme.Hom.appLE_eq_app, RingHom.mem_ker.mp hr]
  exact Ideal.zero_mem _

theorem components_pairwiseDisjoint :
    Pairwise fun i j : Fin 3 => Disjoint (Set.range (curveComponent i).base) (Set.range (curveComponent j).base) := by
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hxi hxj
  obtain ⟨W,v,hxW,_,hv⟩ := exists_componentNeighborhood (x := x) (U := ⊤) trivial
  let p := W.affine.primeIdealOf ⟨x,hxW⟩
  have hp (a : Fin 3) (hxa : x ∈ Set.range (curveComponent a).base) : componentIdeal W.frame a ≤ p.asIdeal := by
    change CycleQ2LiteralMovingDivisorOrbitFrames.translateIdeal W.frame.chart W.carrier W.frame.within _ ≤ _
    rw [← componentKernel _ (rootValues_cube complexRoot complexRoot_quadratic a) _ _ _ (v a) (hv a) W.affine]
    exact ker_le_primeIdealOf_range (curveComponent a) W.affine hxW hxa
  have hle := sup_le (hp i hxi) (hp j hxj)
  rw [Ideal.isCoprime_iff_sup_eq.mp (component_coprime W.frame hij)] at hle
  exact p.isPrime.ne_top (top_le_iff.mp hle)

end CycleQ2LiteralMovingPoleComponents

end

#print axioms CycleQ2LiteralMovingPoleComponents.exists_componentNeighborhood
#print axioms CycleQ2LiteralMovingPoleComponents.components_pairwiseDisjoint
