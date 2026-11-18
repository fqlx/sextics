import Proposal.GeometricLiteralThreefoldSurfaceTestTransport
import Proposal.GeometricLiteralThreefoldTestGauge

/-!
# Restricting the actual ambient test edges to the native surface test lifts

The two affine chart presentations agree through the original threefold
overlap ring. On each native surface intersection the contracted ambient
edge and the edge from its own projective splittings differ by the two
vertex corrections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldSurfaceTestComparison

open MvPolynomial CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldTriangleLifts CycleQ2LiteralThreefoldTangentOverlap
  CycleQ2LiteralThreefoldTestEdges CycleQ2LiteralThreefoldTestGauge
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2LiteralThreefoldSurfaceTestLifts
open CycleQ2LiteralThreefoldKodairaSpencer (P Index)

attribute [local instance] closedComplexAlgebra closedComplexSMul closedComplexModule

private theorem correction_after_index {S : Type} [CommRing S] [Algebra ℂ S]
    (i j : Fin 4) (k : Fin 3) (hj : i.succAbove k = j)
    (g : FixedOverlap i k →ₐ[ℂ] S) (f : T i →ₐ[ℂ] S) (r : T j →ₐ[ℂ] S)
    (hg : g.comp (sourceMap i k) = f)
    (hr : ∀ p : P, g (fixedTargetMap i k (q (i.succAbove k) p)) = r (q j p))
    (z : Lift i S) (z' w : Lift j S) (hn : Normalizes z z')
    (hz : LiesOver z f) (hz' : LiesOver z' r) (hw : LiesOver w r) :
    edgeAt i k g + value (canonical j r) w (fun a => (hw a).symm) =
      value (canonical i f) z (fun a => (hz a).symm) + value z' w (fun a => (hz' a).trans (hw a).symm) := by
  subst j
  have h : g.comp (fixedTargetMap i k) = r := chart_ext _ (fun a => hr (X a))
  subst r
  subst f
  exact nativeEdge_change_of_lifts i k g z z' w hn hz hz' hw

def vertexCorrection (s : Finset Vertex) (v : Vertex) (hv : v ∈ s) :=
  value (canonical (chartIndex v) (fixedPoint s v hv)) (surfaceLift s v hv v.1 ⟨v.2, hv⟩)
    (fun a => (surfaceLift_liesOver s v hv v.1 ⟨v.2, hv⟩ a).symm)

def adaptedEdge (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) :=
  value (surfaceLift s v hv u.1 ⟨u.2,hu⟩) (surfaceLift s v hv v.1 ⟨v.2,hv⟩)
    (fun a => (surfaceLift_liesOver s v hv u.1 ⟨u.2,hu⟩ a).trans
      (surfaceLift_liesOver s v hv v.1 ⟨v.2,hv⟩ a).symm)

/-- The native two-form on the original fixed threefold overlap agrees with
the test edge of the original cubic surface deformation up to its explicit
vertex corrections. -/
theorem ambient_edge_on_surface (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s)
    (k : Fin 3) (h : (chartIndex u).succAbove k = chartIndex v) :
    edgeAt (chartIndex u) k (fixedOverlapPoint s u v hu hv k h) + vertexCorrection s v hv =
      vertexCorrection s u hu + adaptedEdge s u v hu hv :=
  correction_after_index (chartIndex u) (chartIndex v) k h _ _ _
    (fixedOverlapPoint_source s u v hu hv k h) (fixedOverlapPoint_target s u v hu hv k h)
    _ _ _ (surfaceLift_normalizes s u v hu hv u.1 ⟨u.2,hu⟩)
    (surfaceLift_liesOver s u hu u.1 ⟨u.2,hu⟩)
    (surfaceLift_liesOver s v hv u.1 ⟨u.2,hu⟩)
    (surfaceLift_liesOver s v hv v.1 ⟨v.2,hv⟩)

private theorem normalizes_same {S : Type} [CommRing S] [Algebra ℂ S]
    {i : Fin 4} {x y : Lift i S} (hn : Normalizes x y) : x = y := by
  obtain ⟨u,hu,rfl⟩ := hn
  have h : u = 1 := by simpa only [linearValues, Fin.insertNth_apply_same, mul_one] using hu
  subst u
  apply lift_ext
  funext a
  cases a <;> simp [change, changedCoordinate]

private theorem correction_same_index {S : Type} [CommRing S] [Algebra ℂ S]
    (i j : Fin 4) (hij : i = j) (f : T i →ₐ[ℂ] S) (r : T j →ₐ[ℂ] S)
    (z : Lift i S) (z' w : Lift j S) (hn : Normalizes z z')
    (hz : LiesOver z f) (hz' : LiesOver z' r) (hw : LiesOver w r) :
    value (canonical j r) w (fun a => (hw a).symm) =
      value (canonical i f) z (fun a => (hz a).symm) + value z' w (fun a => (hz' a).trans (hw a).symm) := by
  subst j
  obtain rfl := normalizes_same hn
  have e : f = r := chart_ext i (fun a => (hz a).symm.trans (hz' a))
  subst r
  exact value_cocycle (canonical i f) z w _ _

/-- On two vertices with the same weight-one coordinate, the native ambient
edge is zero. The adapted edge is exactly the change of vertex corrections. -/
theorem same_chart_on_surface (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s)
    (h : chartIndex u = chartIndex v) : vertexCorrection s v hv =
      vertexCorrection s u hu + adaptedEdge s u v hu hv :=
  correction_same_index (chartIndex u) (chartIndex v) h _ _ _ _ _
    (surfaceLift_normalizes s u v hu hv u.1 ⟨u.2,hu⟩)
    (surfaceLift_liesOver s u hu u.1 ⟨u.2,hu⟩)
    (surfaceLift_liesOver s v hv u.1 ⟨u.2,hu⟩)
    (surfaceLift_liesOver s v hv v.1 ⟨v.2,hv⟩)

theorem vertexCorrection_restrict {s t : Finset Vertex} (hst : s ⊆ t) (v : Vertex) (hv : v ∈ s) :
    CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap (closedRestrictionAlgHom hst) 2
        (vertexCorrection s v hv) = vertexCorrection t v (hst hv) := by
  unfold vertexCorrection
  rw [value_map]
  simp only [mapLift_canonical, surfaceLift_restrict, fixedPoint_restrict]

theorem adaptedEdge_restrict {s t : Finset Vertex} (hst : s ⊆ t) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s) :
    CycleQ2ExteriorSectionNaturality.exteriorDifferentialMap (closedRestrictionAlgHom hst) 2
        (adaptedEdge s u v hu hv) = adaptedEdge t u v (hst hu) (hst hv) := by
  unfold adaptedEdge
  rw [value_map]
  simp only [surfaceLift_restrict]

end CycleQ2LiteralThreefoldSurfaceTestComparison
end

#print axioms CycleQ2LiteralThreefoldSurfaceTestComparison.ambient_edge_on_surface
#print axioms CycleQ2LiteralThreefoldSurfaceTestComparison.same_chart_on_surface
#print axioms CycleQ2LiteralThreefoldSurfaceTestComparison.vertexCorrection_restrict

