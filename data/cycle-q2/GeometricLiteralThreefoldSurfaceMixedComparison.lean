import Proposal.GeometricLiteralThreefoldSurfaceTestTransport
import Proposal.GeometricLiteralThreefoldMixedGauge
import Proposal.GeometricThreefoldMixedWedge

/-!
# The adapted surface tangent in the mixed ambient comparison

The normalized ambient source and the two actual surface splittings are
evaluated in a common native chart after any restriction of the surface
intersection. The last vector in the comparison is exactly the restriction
of the native surface Kodaira–Spencer derivation. The motion is inserted
before either surface or curve cotangent restriction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldSurfaceMixedComparison

open MvPolynomial CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldChartLift
  CycleQ2LiteralThreefoldLiftDifference CycleQ2LiteralThreefoldResidueCoordinates
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldLiftTransition
  CycleQ2LiteralThreefoldTriangleLifts CycleQ2LiteralThreefoldTangentOverlap
  CycleQ2LiteralThreefoldTestEdges CycleQ2LiteralThreefoldMixedGauge
  CycleQ2ThreefoldMixedCurveForm CycleQ2LiteralThreefoldChartVolume
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionComplex
  CycleQ2LiteralThreefoldSurfaceTestLifts CycleQ2LiteralNativeKodairaSpencer

attribute [local instance] closedComplexAlgebra closedComplexSMul closedComplexModule

variable {A : Type} [CommRing A] [Algebra ℂ A]

private def transportLift {i j : Fin 4} (h : i = j) (x : Lift i A) : Lift j A := h ▸ x

@[simp] private theorem transportLift_coordinates {i j : Fin 4} (h : i = j) (x : Lift i A) :
    (transportLift h x).x = x.x := by subst j; rfl

/-- The genuine ambient lift of the first vertex, in the coordinates of the
second vertex on a native surface intersection. -/
def ambientSource (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s)
    (k : Fin 3) (h : (chartIndex u).succAbove k = chartIndex v) (g : ClosedRing s →ₐ[ℂ] A) :
    Lift (chartIndex v) A :=
  transportLift h (normalizedLift (chartIndex u) k (g.comp (fixedOverlapPoint s u v hu hv k h)))

theorem ambientSource_over (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s)
    (k : Fin 3) (h : (chartIndex u).succAbove k = chartIndex v) (g : ClosedRing s →ₐ[ℂ] A) :
    LiesOver (ambientSource s u v hu hv k h g) (g.comp (fixedPoint s v hv)) := by
  intro a
  rw [ambientSource, transportLift_coordinates, normalizedLift_fst]
  exact congrArg g (fixedOverlapPoint_target s u v hu hv k h (X a))

/-- An identity of ordinary one-forms with the ambient and actual surface
tangents, for every transverse motion along a further surface restriction. -/
theorem mixed_native_surface (s : Finset Vertex) (u v : Vertex) (hu : u ∈ s) (hv : v ∈ s)
    (k : Fin 3) (h : (chartIndex u).succAbove k = chartIndex v) (g : ClosedRing s →ₐ[ℂ] A) :
    let j := chartIndex v
    let f := g.comp (fixedPoint s v hv)
    letI := f.toRingHom.toAlgebra
    letI := IsScalarTower.of_algHom f
    let x := ambientSource s u v hu hv k h g
    let y := canonical j f
    let z := mapLift g (surfaceLift s v hv u.1 ⟨u.2,hu⟩)
    let w := mapLift g (surfaceLift s v hv v.1 ⟨v.2,hv⟩)
    let hx := ambientSource_over s u v hu hv k h g
    let hy := canonical_liesOver j f
    let hz := mappedSurfaceLift_liesOver s v hv u.1 ⟨u.2,hu⟩ g
    let hw := mappedSurfaceLift_liesOver s v hv v.1 ⟨v.2,hv⟩ g
    let ω := (-1 : T j)^j.val • chartVolume j
    let κ := tangent z w hz hw
    (∀ ν : Derivation ℂ (T j) A,
      mixed (tangent x y hx hy) ν ω + mixed (tangent y w hy hw) ν ω =
        mixed (tangent x z hx hz) ν ω + mixed κ ν ω) ∧
      (∀ r : T j, κ r = g (kodairaSpencer s u.1 v.1 ⟨u.2,hu⟩ ⟨v.2,hv⟩ (fixedPoint s v hv r))) := by
  let f := g.comp (fixedPoint s v hv)
  let := f.toRingHom.toAlgebra
  let := IsScalarTower.of_algHom f
  dsimp only
  constructor
  · intro ν
    rw [← CycleQ2ThreefoldMixedWedge.mixed_add_left, ← CycleQ2ThreefoldMixedWedge.mixed_add_left,
      ← tangent_cocycle, ← tangent_cocycle]
  · exact tangent_map_surfaceLift s v hv u.1 v.1 ⟨u.2,hu⟩ ⟨v.2,hv⟩ g

end CycleQ2LiteralThreefoldSurfaceMixedComparison
end

#print axioms CycleQ2LiteralThreefoldSurfaceMixedComparison.mixed_native_surface

