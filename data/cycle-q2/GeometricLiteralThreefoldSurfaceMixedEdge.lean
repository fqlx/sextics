import Proposal.GeometricLiteralThreefoldMixedEdgeGauge
import Proposal.GeometricLiteralThreefoldSurfaceTestTransport
import Proposal.GeometricLiteralThreefoldMixedRestriction

/-!
# The actual native edge and the fitted surface vertices

This formula takes the ambient edge in its fixed threefold overlap ring,
contracts it there against the transverse motion, and identifies both
vertex terms in their respective native chart. The last tangent is the
one supplied by the original projective surface splittings.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldSurfaceMixedEdge

open MvPolynomial CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldTriangleLifts CycleQ2LiteralThreefoldTestEdges
  CycleQ2LiteralThreefoldMixedLiftChange CycleQ2LiteralThreefoldMixedEdgeGauge
  CycleQ2LiteralThreefoldMixedRestriction CycleQ2LiteralThreefoldSurfaceTestLifts
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2LiteralThreefoldTangentOverlap

attribute [local instance] closedComplexAlgebra closedComplexModule closedComplexSMul

variable {S : Type} [CommRing S] [Algebra ℂ S]

theorem map_normalizes {R : Type} [CommRing R] [Algebra ℂ R]
    {i j : Fin 4} (g : R →ₐ[ℂ] S) {x : Lift i R} {y : Lift j R} (h : Normalizes x y) :
    Normalizes (mapLift g x) (mapLift g y) := by
  obtain ⟨u,hu,rfl⟩ := h
  exact ⟨jetMap g u, mapLift_change_inverse g x j u hu, (mapLift_change g x j u hu).symm⟩

private def reindex {i j : Fin 4} (h : i = j) (x : Lift i S) : Lift j S := h ▸ x

private theorem reindex_over {i j : Fin 4} (h : i = j) (f : T i →ₐ[ℂ] S) (r : T j →ₐ[ℂ] S)
    (hr : ∀ p : MvPolynomial (Option (Fin 3)) ℂ, f (q i p) = r (q j p))
    (x : Lift i S) (hx : LiesOver x f) : LiesOver (reindex h x) r := by
  subst j
  exact fun a => (hx a).trans (hr (X a))

private theorem reindex_normalizes {i j k : Fin 4} (h : j = k) (x : Lift i S) (y : Lift j S)
    (hn : Normalizes x y) : Normalizes x (reindex h y) := by subst k; exact hn

variable (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s)
  (k : Fin 3) (h : (chartIndex u).succAbove k = chartIndex v) (g : ClosedRing s →ₐ[ℂ] S)

private abbrev ρ := g.comp (fixedOverlapPoint s u v hu hv k h)
private abbrev a := sourceMap (chartIndex u) k
private abbrev b := fixedTargetMap (chartIndex u) k
private abbrev z := mapLift g (surfaceLift s u hu u.1 ⟨u.2,hu⟩)
private abbrev z' := reindex h.symm (mapLift g (surfaceLift s v hv u.1 ⟨u.2,hu⟩))
private abbrev w := reindex h.symm (mapLift g (surfaceLift s v hv v.1 ⟨v.2,hv⟩))

private theorem sz : LiesOver (z s u hu g) ((ρ s u v hu hv k h g).comp (a u k)) := by
  change LiesOver _ (g.comp ((fixedOverlapPoint s u v hu hv k h).comp (a u k)))
  rw [fixedOverlapPoint_source]
  exact mappedSurfaceLift_liesOver _ _ _ _ _ _

private theorem tz : LiesOver (z' s u v hu hv k h g) ((ρ s u v hu hv k h g).comp (b u k)) :=
  reindex_over h.symm (g.comp (fixedPoint s v hv)) ((ρ s u v hu hv k h g).comp (b u k)) (fun p => congrArg g
    (fixedOverlapPoint_target s u v hu hv k h p).symm) _ (mappedSurfaceLift_liesOver _ _ _ _ _ _)

private theorem tw : LiesOver (w s u v hv k h g) ((ρ s u v hu hv k h g).comp (b u k)) :=
  reindex_over h.symm (g.comp (fixedPoint s v hv)) ((ρ s u v hu hv k h g).comp (b u k)) (fun p => congrArg g
    (fixedOverlapPoint_target s u v hu hv k h p).symm) _ (mappedSurfaceLift_liesOver _ _ _ _ _ _)

theorem surface_mixed_edge :
    let r := ρ s u v hu hv k h g
    letI := r.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom r
    ∀ ν : Derivation ℂ (FixedOverlap (chartIndex u) k) S,
      contractRestrict ν (nativeEdge (chartIndex u) k) +
        vertexMixed (b u k) (canonical _ (r.comp (b u k))) (w s u v hv k h g)
          (canonical_liesOver _ _) (tw s u v hu hv k h g) ν =
        vertexMixed (a u k) (canonical _ (r.comp (a u k))) (z s u hu g)
          (canonical_liesOver _ _) (sz s u v hu hv k h g) ν +
        vertexMixed (b u k) (z' s u v hu hv k h g) (w s u v hv k h g)
          (tz s u v hu hv k h g) (tw s u v hu hv k h g) ν := by
  let r := ρ s u v hu hv k h g
  let := r.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom r
  intro ν
  apply nativeEdge_mixed_change_of_lifts
  exact reindex_normalizes h.symm _ _ (map_normalizes g (surfaceLift_normalizes s u v hu hv u.1 ⟨u.2,hu⟩))

end CycleQ2LiteralThreefoldSurfaceMixedEdge
end

#print axioms CycleQ2LiteralThreefoldSurfaceMixedEdge.surface_mixed_edge
