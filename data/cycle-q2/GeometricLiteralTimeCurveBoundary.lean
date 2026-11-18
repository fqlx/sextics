import Proposal.GeometricLiteralTimeCurveDimension
import Proposal.GeometricDenseOpenTotalFractions
import Mathlib.RingTheory.KrullDimension.Basic

/-!
# Boundary points of the proper parameter curve

On each affine chart, a regular function cuts out a closed set containing the
boundary. Every prime containing this function is maximal by the dimension
bound, so each is a minimal prime over the principal ideal. Quasi-compactness
then gives finiteness of the full boundary. The completion and normalization
are Jacobson schemes over the complex field, so their finite closed boundaries
consist of closed points.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeCurveBoundary

open AlgebraicGeometry CategoryTheory Set TopologicalSpace

private theorem finite_affine_boundary (A : Type) [CommRing A] [_root_.IsReduced A]
    [IsNoetherianRing A] [Ring.KrullDimLE 1 A] (W : Opens (PrimeSpectrum A))
    (hd : Dense (W : Set (PrimeSpectrum A))) : (W : Set (PrimeSpectrum A))ᶜ.Finite := by
  classical
  obtain ⟨r, hr, hW⟩ := CycleQ2DenseOpenTotalFractions.exists_regular_basicOpen A W hd
  let I : Ideal A := Ideal.span {r}
  have hmax {q : Ideal A} (hq : q.IsPrime) (hrq : r ∈ q) : q.IsMaximal :=
    (Ring.krullDimLE_one_iff.mp inferInstance q hq).resolve_left fun hm =>
      Set.disjoint_left.mp (Ideal.disjoint_nonZeroDivisors_of_mem_minimalPrimes hm) hrq hr
  have hi : Function.Injective (PrimeSpectrum.asIdeal : PrimeSpectrum A → Ideal A) :=
    fun _ _ h => PrimeSpectrum.ext h
  apply ((Ideal.finite_minimalPrimes_of_isNoetherianRing A I).preimage hi.injOn).subset
  intro p hp
  have hrp : r ∈ p.asIdeal := by
    by_contra hn
    exact hp (hW hn)
  obtain ⟨q, hq, hqp⟩ := Ideal.exists_minimalPrimes_le (I := I) (J := p.asIdeal)
    (Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hrp))
  have hqr : r ∈ q := hq.1.2 (Ideal.subset_span (Set.mem_singleton r))
  have heq := (hmax hq.1.1 hqr).eq_of_le p.isPrime.ne_top hqp
  change p.asIdeal ∈ I.minimalPrimes
  rwa [← heq]

private theorem finite_boundary_of_charts {X Y : Scheme.{0}} (j : X ⟶ Y)
    [IsOpenImmersion j] [IsDominant j] [AlgebraicGeometry.IsReduced Y]
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType p] [QuasiCompact p]
    (hdim : ∀ V : Y.affineOpens, Ring.KrullDimLE 1 Γ(Y, V)) :
    (Set.range j)ᶜ.Finite ∧ (Set.range j)ᶜ ⊆ closedPoints Y := by
  classical
  let : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace p
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian p
  let : JacobsonSpace Y := LocallyOfFiniteType.jacobsonSpace p
  let W := j.opensRange
  have hd : Dense (W : Set Y) := j.denseRange
  have patch (V : Y.affineOpens) : ((W : Set Y)ᶜ ∩ (V.1 : Set Y)).Finite := by
    let : IsNoetherianRing Γ(Y, V) := IsLocallyNoetherian.component_noetherian V
    let := hdim V
    let f := V.2.fromSpec
    have hf := finite_affine_boundary Γ(Y, V) (f ⁻¹ᵁ W)
      (hd.preimage f.isOpenEmbedding.isOpenMap)
    change (f ⁻¹' (W : Set Y)ᶜ).Finite at hf
    simpa only [Set.image_preimage_eq_inter_range, V.2.range_fromSpec, f] using hf.image f
  have cover : Set.univ ⊆ ⋃ V : Y.affineOpens, (V.1 : Set Y) := by
    intro x _
    obtain ⟨V, hV, hx, _⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top x)
    exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hx⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun V : Y.affineOpens => (V.1 : Set Y)) (fun V => V.1.isOpen) cover
  have hfin : (W : Set Y)ᶜ.Finite := by
    apply (t.finite_toSet.biUnion fun V _ => patch V).subset
    intro x hx
    obtain ⟨V, hV⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ x))
    obtain ⟨hV, hxV⟩ := Set.mem_iUnion.mp hV
    exact Set.mem_iUnion₂.mpr ⟨V, hV, hx, hxV⟩
  refine ⟨hfin, ?_⟩
  let B := (W : Set Y)ᶜ
  have hB : IsClosed B := W.isOpen.isClosed_compl
  let : Finite B := hfin
  let : JacobsonSpace B := JacobsonSpace.of_isClosedEmbedding hB.isClosedEmbedding_subtypeVal
  intro x hx
  change IsClosed ({x} : Set Y)
  have hsing : IsClosed ({⟨x, hx⟩} : Set B) := isClosed_discrete _
  simpa only [Set.image_singleton] using hB.isClosedEmbedding_subtypeVal.isClosedMap _ hsing

open CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralTimeCurveCompletion
  CycleQ2LiteralTimeCurveNormalization CycleQ2LiteralTimeCurveDimension

/-- The projective completion adds only finitely many closed points. -/
theorem completion_boundary (U : Curve.Opens) :
    (Set.range (inclusion U))ᶜ.Finite ∧
      (Set.range (inclusion U))ᶜ ⊆ closedPoints (Completion U) :=
  finite_boundary_of_charts (inclusion U) (structureMap U) (fun V => completion_chart U V.2)

/-- The finite normalization also adds only finitely many closed points to the same smooth open. -/
theorem normalization_boundary (U : Curve.Opens) :
    (Set.range (openInclusion U))ᶜ.Finite ∧
      (Set.range (openInclusion U))ᶜ ⊆ closedPoints (Normalization U) :=
  finite_boundary_of_charts (openInclusion U) (toComplexPoint U) (fun V => normalization_chart U V.2)

end CycleQ2LiteralTimeCurveBoundary
end

#print axioms CycleQ2LiteralTimeCurveBoundary.completion_boundary
#print axioms CycleQ2LiteralTimeCurveBoundary.normalization_boundary
