import Proposal.GeometricLiteralNegativeTwistWeight
import Proposal.GeometricLiteralMovingIdealExact
import Proposal.GeometricLiteralTwistedOrbitMembership
import Proposal.GeometricLiteralTwistHOne
import Proposal.GeometricLiteralMovingGlobalFunctions

/-!
# Global functions on the moving projective curve

A primitive of a moving-ideal cocycle in the ambient negative-fourth twist
has restrictions agreeing on the orbit. Negative-degree vanishing forces
its three coordinates into the orbit ideal. They therefore give a primitive
in the actual moving ideal. The affine lifts of a global function on the
curve can consequently be corrected and glued on the surface.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingCurveConnected

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2GeometricModuleLocalIso
  CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionSheaf CycleQ2SeedSectionSheafKernel
  CycleQ2SeedSectionSheafIso CycleQ2SeedSectionAffineInjective
  CycleQ2SeedSectionSheafSections CycleQ2LiteralMovingIdealExact
  CycleQ2GeometricSurfaceCoordinates CycleQ2ProjectiveCoordinateCohomology
  CycleQ2SurfaceSectionCoefficients CycleQ2LiteralCoordinateTwistPrimitives
  CycleQ2LiteralTwistHOne CycleQ2LiteralNegativeTwistWeight CycleQ2CoordinateCechTrace
  CycleQ2LiteralOrbitNegativeSections CycleQ2LiteralTwistedOrbitMembership

open CycleQ2LiteralMovingGlobalFunctions (IdealPrimitive moving_global_surjective)
open CycleQ2CechTwoToDerived (app app_res app_injective)

private abbrev F := addSheaf twistedIdeal
private def inclusion : F ⟶ twist (-4) := (SheafOfModules.toSheaf Surface.ringCatSheaf).map orbitInclusion

private theorem cone_mem_iff (I : Finset (Fin 3)) (hI : I.Nonempty) (a : Sections (twist (-4)) (U I)) :
    toCone (-4) I hI a ∈ chartOrbitIdeal I ↔ ∃ x : Sections F (U I), app inclusion _ x = a := by
  let i := I.min' hI
  let hi := Finset.min'_mem I hI
  change encode (-4) I hI i hi (coordinate (-4) i (U I) (intersection_le_chart 57 1 i hi) a) ∈ chartOrbitIdeal I ↔ _
  rw [encode_mem_iff]
  constructor
  · rintro ⟨x,hx⟩
    refine ⟨x, (coordinateEquiv (-4) i _ (intersection_le_chart 57 1 i hi)).injective ?_⟩
    exact (coordinate_orbitInclusion i _ (intersection_le_chart 57 1 i hi) x).trans hx
  · rintro ⟨x,rfl⟩
    exact ⟨x,(coordinate_orbitInclusion i _ (intersection_le_chart 57 1 i hi) x).symm⟩

private theorem orbit_primitive (c : One F vertex) (hc : IsOneCocycle F vertex c) :
    ∃ p : Zero F vertex, ∀ i j, i < j →
      res F (inf_le_right : vertex i ⊓ vertex j ≤ vertex j) (p j) - res F inf_le_left (p i) = c i j := by
  let d := mapOne vertex inclusion c
  obtain ⟨p,hp⟩ := primitive (-4) d (mapOne_closed vertex inclusion c hc)
  let q (i : Fin 3) := toCone (-4) {i} (by simp) (p i)
  have hweight (i : Fin 3) : q i ∈ coordinateLocalWeight 57 (-4) {i} :=
    encode_neg_four_weight {i} (Finset.singleton_nonempty i) _ (Finset.min'_mem _ _) _
  have hedge (i j : Fin 3) (hij : i < j) :
      coordinateRestriction 57 1 (s := {j}) (t := {i,j}) (by simp) (q j) -
        coordinateRestriction 57 1 (s := {i}) (t := {i,j}) (by simp) (q i) ∈ chartOrbitIdeal {i,j} := by
    let A : ({i} : Finset (Fin 3)) ⊆ {i,j} := by simp
    let B : ({j} : Finset (Fin 3)) ⊆ {i,j} := by simp
    let hi := coordinateIntersection_mono 57 1 A
    let hj := coordinateIntersection_mono 57 1 B
    have h := congrArg (res (twist (-4)) (le_inf hi hj)) (hp i j hij)
    rw [map_sub, res_comp, res_comp] at h
    change _ - _ = edgeValue (twist (-4)) vertex (mapOne vertex inclusion c) i j _ hi hj at h
    rw [edgeValue_mapOne] at h
    change coordinateRestriction 57 1 B (toCone (-4) {j} (by simp) (p j)) -
      coordinateRestriction 57 1 A (toCone (-4) {i} (by simp) (p i)) ∈ chartOrbitIdeal {i,j}
    rw [toCone_restrict (-4) (by simp) (by simp) B, toCone_restrict (-4) (by simp) (by simp) A, ← map_sub,
      (cone_mem_iff _ (by simp) _)]
    exact ⟨_,h.symm⟩
  have hq := negative_coordinate_family_mem_ideal (-4) (by decide) q hweight
    (hedge 0 2 (by decide)) (hedge 1 2 (by decide))
  choose s hs using fun i => (cone_mem_iff {i} (by simp) (p i)).mp (hq i)
  refine ⟨s,fun i j hij => ?_⟩
  let V := vertex i ⊓ vertex j
  have hi : V ≤ Patch i := inf_le_left.trans (intersection_le_chart 57 1 i (Finset.mem_singleton_self i))
  have hinj : Function.Injective (app inclusion V) := by
    intro x y hxy
    apply CycleQ2SeedSectionDivisorFrames.sourceCoordinate_injective i V hi
    have h := congrArg (coordinate (-4) i V hi) hxy
    exact (coordinate_orbitInclusion i V hi x).symm.trans (h.trans (coordinate_orbitInclusion i V hi y))
  apply hinj
  rw [map_sub, app_res, app_res, hs, hs]
  exact hp i j hij

theorem movingIdealPrimitive (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) : IdealPrimitive t := by
  let e := (SheafOfModules.toSheaf Surface.ringCatSheaf).mapIso (twistedIdealCurveIso t ht)
  intro c hc
  obtain ⟨p,hp⟩ := orbit_primitive (mapOne vertex e.inv c) (mapOne_closed vertex e.inv c hc)
  refine ⟨mapZero vertex e.hom p,fun i j hij => ?_⟩
  apply app_injective e.inv _
  change app e.inv _ (res _ inf_le_right (app e.hom _ (p j)) - res _ inf_le_left (app e.hom _ (p i))) = _
  rw [map_sub, app_res, app_res]
  rw [CycleQ2CechTwoToDerived.app_comp, CycleQ2CechTwoToDerived.app_comp, e.hom_inv_id]
  exact hp i j hij

/-- Every regular vector gives a connected curve on the original surface. -/
theorem movingConnected (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    ConnectedSpace (CycleQ2LiteralMovingGlobalFunctions.Curve t) :=
  CycleQ2LiteralMovingGlobalFunctions.moving_connected t (movingIdealPrimitive t ht)

/-- Every global regular function on this curve is a unique complex constant. -/
def movingFunctionsEquiv (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    ℂ ≃+* Γ(CycleQ2LiteralMovingGlobalFunctions.Curve t, ⊤) :=
  CycleQ2LiteralMovingGlobalFunctions.movingGlobalFunctionsEquiv t (movingIdealPrimitive t ht)

end CycleQ2LiteralMovingCurveConnected
end

#print axioms CycleQ2LiteralMovingCurveConnected.movingIdealPrimitive

#print axioms CycleQ2LiteralMovingCurveConnected.movingConnected
#print axioms CycleQ2LiteralMovingCurveConnected.movingFunctionsEquiv
