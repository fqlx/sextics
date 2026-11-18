import Proposal.GeometricLiteralNegativeTwistDescent
import Proposal.GeometricLiteralCoordinateTwistPrimitives
import Proposal.GeometricLiteralCoordinateTwist

/-!
# First cohomology of integral coordinate twists on the literal surface

The chart coordinate of a twisted section gives an ordinary cone section
after multiplication by the appropriate power of that coordinate. These
maps are independent of the chosen chart on an intersection. The inverse
construction projects a cone section to the required degree, so a cone
primitive for three edges gives a primitive in the actual twisted sheaf.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralTwistHOne

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace Opposite
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2GeometricProjectiveHOne
  CycleQ2SeedProjectiveImageCocycle CycleQ2LiteralMovingIdealExact
  CycleQ2GeometricSurfaceCoordinates CycleQ2ProjectiveCoordinateCohomology
  CycleQ2SurfaceSectionCoefficients CycleQ2LiteralCoordinateTwistPrimitives
  CycleQ2SeedSectionSheafLocal CycleQ2SeedSectionSheafGlobal

local instance sheafHasExt : HasExt.{1} (AbSheaf Surface) := HasExt.standard _

abbrev twist (k : ℤ) := CycleQ2GeometricModuleLocalIso.addSheaf (ambientTwist k)
abbrev vertex (i : Fin 3) := U {i}

private theorem within {I : Finset (Fin 3)} (i : Fin 3) (hi : i ∈ I) : U I ≤ Patch i :=
  intersection_le_chart 57 1 i hi

private theorem le_vertex {I : Finset (Fin 3)} (i : Fin 3) (hi : i ∈ I) : U I ≤ vertex i :=
  coordinateIntersection_mono 57 1 (Finset.singleton_subset_iff.mpr hi)

private theorem vertex_top : (⨆ i, vertex i) = ⊤ := by
  simpa only [vertex, U, coordinateIntersection_singleton] using coordinate_cover 57 1 one_ne_zero

private theorem vertex_hOne (k : ℤ) (i : Fin 3) : Subsingleton ((twist k).H' 1 (vertex i)) := by
  let frame : PatchIso (twist k) (structureAdditiveSheaf Surface) (vertex i) := {
    app := fun W hW => (coordinateEquiv k i W (hW.trans (within i (Finset.mem_singleton_self i)))).toAddEquiv
    naturality := fun h hW s => coordinate_restrict k i h (hW.trans (within i (Finset.mem_singleton_self i))) s }
  exact affineFrameHOne_subsingleton (coordinateChart 57 1 {i} (by simp))
    (twist k) (overIsoOfPatchIso frame)

def toConeAt (k : ℤ) (I : Finset (Fin 3)) (hI : I.Nonempty) (i : Fin 3) (hi : i ∈ I) :
    Sections (twist k) (U I) →+ cone I :=
  (encode k I hI i hi).comp (coordinate k i (U I) (within i hi)).toAddMonoidHom

theorem toConeAt_eq (k : ℤ) (I : Finset (Fin 3)) (hI : I.Nonempty)
    (i j : Fin 3) (hi : i ∈ I) (hj : j ∈ I) (s : Sections (twist k) (U I)) :
    toConeAt k I hI i hi s = toConeAt k I hI j hj s := by
  change encode k I hI i hi (coordinate k i _ _ s) = _
  rw [coordinate_transition k i j (U I) (within i hi) (within j hj)]
  exact encode_change k I hI i j hi hj _

def toCone (k : ℤ) (I : Finset (Fin 3)) (hI : I.Nonempty) :=
  toConeAt k I hI _ (Finset.min'_mem I hI)

theorem toCone_restrict (k : ℤ) {I J : Finset (Fin 3)} (hI : I.Nonempty) (hJ : J.Nonempty)
    (h : I ⊆ J) (s : Sections (twist k) (U I)) :
    coordinateRestriction 57 1 h (toCone k I hI s) =
      toCone k J hJ (res (twist k) (coordinateIntersection_mono 57 1 h) s) := by
  let i := I.min' hI
  have hi : i ∈ I := Finset.min'_mem I hI
  rw [show toCone k J hJ _ = toConeAt k J hJ i (h hi) _ from toConeAt_eq k J hJ _ i _ (h hi) _]
  change coordinateRestriction 57 1 h (encode k I hI i hi (coordinate k i _ _ s)) =
    encode k J hJ i (h hi) (coordinate k i _ _ _)
  rw [encode_restrict k hI hJ h i hi]
  apply congrArg (encode k J hJ i (h hi))
  exact coordinate_restrict k i _ _ s

def fromConeAt (k : ℤ) (I : Finset (Fin 3)) (hI : I.Nonempty) (i : Fin 3) (hi : i ∈ I) :
    cone I →+ Sections (twist k) (U I) :=
  (coordinateEquiv k i (U I) (within i hi)).symm.toAddEquiv.toAddMonoidHom.comp (decode k I hI i hi)

private theorem coordinate_fromConeAt (k : ℤ) (I : Finset (Fin 3)) (hI : I.Nonempty)
    (i : Fin 3) (hi : i ∈ I) (a : cone I) :
    coordinate k i (U I) (within i hi) (fromConeAt k I hI i hi a) = decode k I hI i hi a :=
  (coordinateEquiv k i (U I) (within i hi)).apply_symm_apply _

theorem fromConeAt_eq (k : ℤ) (I : Finset (Fin 3)) (hI : I.Nonempty)
    (i j : Fin 3) (hi : i ∈ I) (hj : j ∈ I) (a : cone I) :
    fromConeAt k I hI i hi a = fromConeAt k I hI j hj a := by
  apply coordinate_injective k i (U I) (within i hi)
  rw [coordinate_fromConeAt, coordinate_transition k i j (U I) (within i hi) (within j hj),
    coordinate_fromConeAt]
  exact decode_change k I hI i j hi hj a

def fromCone (k : ℤ) (I : Finset (Fin 3)) (hI : I.Nonempty) :=
  fromConeAt k I hI _ (Finset.min'_mem I hI)

theorem fromCone_toCone (k : ℤ) (I : Finset (Fin 3)) (hI : I.Nonempty)
    (s : Sections (twist k) (U I)) : fromCone k I hI (toCone k I hI s) = s := by
  let i := I.min' hI
  have hi : i ∈ I := Finset.min'_mem I hI
  apply coordinate_injective k i (U I) (within i hi)
  change coordinate k i _ _ (fromConeAt k I hI i hi _) = _
  rw [coordinate_fromConeAt]
  exact decode_encode k I hI i hi _

theorem fromCone_restrict (k : ℤ) {I J : Finset (Fin 3)} (hI : I.Nonempty) (hJ : J.Nonempty)
    (h : I ⊆ J) (a : cone I) :
    res (twist k) (coordinateIntersection_mono 57 1 h) (fromCone k I hI a) =
      fromCone k J hJ (coordinateRestriction 57 1 h a) := by
  let i := I.min' hI
  have hi : i ∈ I := Finset.min'_mem I hI
  rw [show fromCone k J hJ _ = fromConeAt k J hJ i (h hi) _ from fromConeAt_eq k J hJ _ i _ (h hi) _]
  apply coordinate_injective k i (U J) (within i (h hi))
  change coordinate k i _ _ (moduleRes (ambientTwist k) _ (fromConeAt k I hI i hi a)) = _
  rw [← coordinate_restrict k i (coordinateIntersection_mono 57 1 h) (within i hi),
    coordinate_fromConeAt, coordinate_fromConeAt]
  exact decode_restrict k hI hJ h i hi a

def pairValue (k : ℤ) (c : One (twist k) vertex) (i j : Fin 3) :
    Sections (twist k) (U {i,j}) := edgeValue (twist k) vertex c i j _
      (le_vertex i (by simp)) (le_vertex j (by simp))

private theorem pairValue_restrict (k : ℤ) (c : One (twist k) vertex)
    (i j : Fin 3) (h : ({i,j} : Finset (Fin 3)) ⊆ Finset.univ) :
    res (twist k) (coordinateIntersection_mono 57 1 h) (pairValue k c i j) =
    edgeValue (twist k) vertex c i j (U Finset.univ)
      (le_vertex i (Finset.mem_univ i)) (le_vertex j (Finset.mem_univ j)) := by
  unfold pairValue edgeValue
  rw [res_comp]

def encodedEdge (k : ℤ) (c : One (twist k) vertex) (i j : Fin 3) :=
  toCone k {i,j} (by simp) (pairValue k c i j)

private theorem encodedEdge_restrict (k : ℤ) (c : One (twist k) vertex) (i j : Fin 3) :
    coordinateRestriction 57 1 (Finset.subset_univ _) (encodedEdge k c i j) =
      toCone k Finset.univ ⟨0,Finset.mem_univ 0⟩ (edgeValue (twist k) vertex c i j (U Finset.univ)
        (le_vertex i (Finset.mem_univ i)) (le_vertex j (Finset.mem_univ j))) := by
  unfold encodedEdge
  rw [toCone_restrict k (by simp) ⟨0,Finset.mem_univ 0⟩ (Finset.subset_univ {i,j}),
    pairValue_restrict k c i j (Finset.subset_univ _)]

theorem encodedEdge_closed (k : ℤ) (c : One (twist k) vertex) (hc : IsOneCocycle (twist k) vertex c) :
    coordinateRestriction 57 1 (Finset.subset_univ _) (encodedEdge k c 0 1) -
      coordinateRestriction 57 1 (Finset.subset_univ _) (encodedEdge k c 0 2) +
      coordinateRestriction 57 1 (Finset.subset_univ _) (encodedEdge k c 1 2) = 0 := by
    have htr := hc 0 1 2 (U Finset.univ) (le_vertex 0 (Finset.mem_univ 0))
      (le_vertex 1 (Finset.mem_univ 1)) (le_vertex 2 (Finset.mem_univ 2))
    rw [encodedEdge_restrict, encodedEdge_restrict, encodedEdge_restrict]
    let e (i j : Fin 3) := edgeValue (twist k) vertex c i j (U Finset.univ)
      (le_vertex i (Finset.mem_univ i)) (le_vertex j (Finset.mem_univ j))
    have he : e 0 1 - e 0 2 + e 1 2 = 0 := by
      dsimp only [e, edgeValue]
      linear_combination (norm := abel) -htr
    simpa only [map_sub, map_add, map_zero] using
      congrArg (toCone k Finset.univ ⟨0,Finset.mem_univ 0⟩) he

/-- Decoding any three cone primitives solves the same three edge equations
in the actual sheaf. -/
theorem decoded_edges (k : ℤ) (c : One (twist k) vertex) (t : (i : Fin 3) → cone {i})
    (ht : ∀ i j, i < j → encodedEdge k c i j =
      coordinateRestriction 57 1 (s := {j}) (t := {i,j}) (by simp) (t j) -
      coordinateRestriction 57 1 (s := {i}) (t := {i,j}) (by simp) (t i)) (i j : Fin 3) (hij : i < j) :
    res (twist k) (inf_le_right : vertex i ⊓ vertex j ≤ vertex j) (fromCone k {j} (by simp) (t j)) -
      res (twist k) inf_le_left (fromCone k {i} (by simp) (t i)) = c i j := by
  let hji : ({j} : Finset (Fin 3)) ⊆ {i,j} := by simp
  let hii : ({i} : Finset (Fin 3)) ⊆ {i,j} := by simp
  have hpair := congrArg (fromCone k {i,j} (by simp)) (ht i j hij)
  change fromCone k {i,j} _ (toCone k {i,j} _ _) = _ at hpair
  rw [fromCone_toCone, map_sub, ← fromCone_restrict k (by simp) (by simp) hji,
    ← fromCone_restrict k (by simp) (by simp) hii] at hpair
  have hV : vertex i ⊓ vertex j ≤ U {i,j} := by
    simpa only [vertex, U, coordinateIntersection_singleton, coordinateIntersection_pair] using
      (le_refl (coordinateOpen 57 1 i ⊓ coordinateOpen 57 1 j))
  have hout := congrArg (res (twist k) hV) hpair.symm
  simpa only [map_sub, pairValue, edgeValue, res_comp, res_self] using hout

/-- A cone primitive that lifts on each vertex to a subsheaf gives a
primitive of the original subsheaf cocycle. -/
theorem primitive_in_subsheaf (k : ℤ) {F : AbSheaf Surface} (f : F ⟶ twist k) [Mono f]
    (c : One F vertex) (t : (i : Fin 3) → cone {i})
    (ht : ∀ i j, i < j → encodedEdge k (mapOne vertex f c) i j =
      coordinateRestriction 57 1 (s := {j}) (t := {i,j}) (by simp) (t j) -
      coordinateRestriction 57 1 (s := {i}) (t := {i,j}) (by simp) (t i))
    (hlift : ∀ i, ∃ a : Sections F (vertex i),
      CycleQ2CechTwoToDerived.app f (vertex i) a = fromCone k {i} (by simp) (t i)) :
    ∃ p : Zero F vertex, ∀ i j, i < j →
      res F (inf_le_right : vertex i ⊓ vertex j ≤ vertex j) (p j) -
        res F inf_le_left (p i) = c i j := by
  choose p hp using hlift
  refine ⟨p, fun i j hij => ?_⟩
  apply CycleQ2CechTwoToDerived.app_injective f (vertex i ⊓ vertex j)
  rw [map_sub, CycleQ2CechTwoToDerived.app_res, CycleQ2CechTwoToDerived.app_res, hp, hp]
  exact decoded_edges k (mapOne vertex f c) t ht i j hij

/-- Every cocycle on the coordinate cover admits an actual twist primitive. -/
theorem primitive (k : ℤ) (c : One (twist k) vertex) (hc : IsOneCocycle (twist k) vertex c) :
    ∃ p : Zero (twist k) vertex, ∀ i j, i < j →
      res (twist k) (inf_le_right : vertex i ⊓ vertex j ≤ vertex j) (p j) -
        res (twist k) inf_le_left (p i) = c i j := by
  obtain ⟨x,y,z, h01,h02,h12⟩ := cone_first_exact _ _ _ (encodedEdge_closed k c hc)
  let t : (i : Fin 3) → cone {i} := fun i => match i with
    | 0 => x | 1 => y | 2 => z
  have ht (i j : Fin 3) (hij : i < j) : encodedEdge k c i j =
      coordinateRestriction 57 1 (s := {j}) (t := {i,j}) (by simp) (t j) -
      coordinateRestriction 57 1 (s := {i}) (t := {i,j}) (by simp) (t i) := by
    fin_cases i <;> fin_cases j <;>
      first | exact h01 | exact h02 | exact h12 | exact absurd hij (by decide)
  exact ⟨fun i => fromCone k {i} (by simp) (t i), decoded_edges k c t ht⟩

theorem twist_hOne_subsingleton (k : ℤ) : Subsingleton ((twist k).H' 1 ⊤) :=
  CycleQ2LiteralNegativeTwistDescent.hOne_subsingleton_of_three_edges
    (twist k) vertex vertex_top (vertex_hOne k) (primitive k)

end CycleQ2LiteralTwistHOne

end

#print axioms CycleQ2LiteralTwistHOne.primitive_in_subsheaf
#print axioms CycleQ2LiteralTwistHOne.twist_hOne_subsingleton
