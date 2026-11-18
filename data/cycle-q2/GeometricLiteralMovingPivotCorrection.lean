import Proposal.GeometricLiteralMovingPivotPrincipal
import Proposal.GeometricMovingPivotRingSplittings
import Proposal.GeometricLiteralProjectiveDeformationCover

/-!
# The moving edge correction is natural on the true pivot opens

Restrictions of the two localized rings are obtained through their
structure sheaves. They preserve the native ring splitting and epsilon
coefficient, hence also the normalized correction of each lifted unit.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingPivotCorrection

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2GeometricKernelLocalization CycleQ2GeometricSquareZeroSplittings
  CycleQ2MovingPivotRingSplittings CycleQ2LiteralMovingPivotPrincipal
  CycleQ2LiteralProjectiveDeformation CycleQ2LiteralProjectiveDeformationCover
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionRestrictions
  CycleQ2LiteralProjectiveIntersectionSplittings CycleQ2LiteralProjectiveIntersectionKernel
  CycleQ2LiteralProjectiveIntersectionComplex CycleQ2LiteralMovingDivisorChern

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexAlgebra
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexSMul
  CycleQ2LiteralProjectiveIntersectionComplex.thickComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.closedComplexModule
  CycleQ2LiteralProjectiveIntersectionComplex.complexReductionTower
  CycleQ2GeometricKernelLocalization.localReductionAlgebra

private abbrev X := CycleQ2CartierProjectiveCover.projectiveSurface 57 1
private abbrev Y := projectiveDeformation

structure Chart where
  vertices : Finset Vertex
  nonempty : vertices.Nonempty
  denominator : ThickRing vertices

namespace Chart

variable (A B : Chart)

abbrev C := ClosedAt (ThickRing A.vertices) (ClosedRing A.vertices) A.denominator
abbrev E := ThickAt (ThickRing A.vertices) A.denominator
abbrev closed := principalOpen A.vertices A.nonempty (nativeReduction _ A.denominator)
abbrev thick := thickPrincipalOpen A.vertices A.nonempty A.denominator
abbrev closedValue := closedPrincipalEquiv A.vertices A.nonempty (nativeReduction _ A.denominator)
abbrev thickValue := thickPrincipalEquiv A.vertices A.nonempty A.denominator
abbrev kernelEquiv := localizedKernelEquiv (ThickRing A.vertices) (ClosedRing A.vertices) (epsilonKernelEquiv _) A.denominator

abbrev closedRes (h : B.closed ≤ A.closed) : A.C →+* B.C :=
  B.closedValue.symm.toRingHom.comp ((X.presheaf.map (homOfLE h).op).hom.comp A.closedValue.toRingHom)

theorem thick_le (h : B.closed ≤ A.closed) : B.thick ≤ A.thick := by
  have h' : closedFiber ⁻¹ᵁ B.thick ≤ closedFiber ⁻¹ᵁ A.thick := by
    rw [preimage_thickPrincipal, preimage_thickPrincipal]
    exact h
  intro y hy
  obtain ⟨x,rfl⟩ := closedFiber_surjective y
  exact h' (show x ∈ closedFiber ⁻¹ᵁ B.thick from hy)

abbrev thickRes (h : B.closed ≤ A.closed) : A.E →+* B.E :=
  B.thickValue.symm.toRingHom.comp ((Y.presheaf.map (homOfLE (thick_le A B h)).op).hom.comp A.thickValue.toRingHom)

theorem closedRes_value (h : B.closed ≤ A.closed) (x : A.C) :
    B.closedValue (closedRes A B h x) = X.presheaf.map (homOfLE h).op (A.closedValue x) :=
  B.closedValue.apply_symm_apply _

theorem thickRes_value (h : B.closed ≤ A.closed) (x : A.E) :
    B.thickValue (thickRes A B h x) = Y.presheaf.map (homOfLE (thick_le A B h)).op (A.thickValue x) :=
  B.thickValue.apply_symm_apply _

private theorem restrict_twice {S : Scheme.{0}} {U V W : S.Opens} (i : V ≤ U) (j : W ≤ V) (x : Γ(S,U)) :
    S.presheaf.map (homOfLE j).op (S.presheaf.map (homOfLE i).op x) =
      S.presheaf.map (homOfLE (j.trans i)).op x := by
  exact (ConcreteCategory.congr_hom (S.presheaf.map_comp (homOfLE i).op (homOfLE j).op) x).symm

theorem closedRes_base (h : B.closed ≤ A.closed) (hst : A.vertices ⊆ B.vertices) (x : ClosedRing A.vertices) :
    closedRes A B h (algebraMap (ClosedRing A.vertices) A.C x) =
      algebraMap (ClosedRing B.vertices) B.C (closedRestriction hst x) := by
  apply B.closedValue.injective
  rw [closedRes_value, closedPrincipalEquiv_base A.vertices A.nonempty (nativeReduction _ A.denominator) x,
    closedPrincipalEquiv_base B.vertices B.nonempty (nativeReduction _ B.denominator) (closedRestriction hst x),
    ← closedSectionsEquiv_restrict A.nonempty B.nonempty hst x, restrict_twice, restrict_twice]

theorem thickRes_base (h : B.closed ≤ A.closed) (hst : A.vertices ⊆ B.vertices) (x : ThickRing A.vertices) :
    thickRes A B h (algebraMap (ThickRing A.vertices) A.E x) =
      algebraMap (ThickRing B.vertices) B.E (thickRestriction hst x) := by
  apply B.thickValue.injective
  rw [thickRes_value, thickPrincipalEquiv_base A.vertices A.nonempty A.denominator x,
    thickPrincipalEquiv_base B.vertices B.nonempty B.denominator (thickRestriction hst x),
    ← thickSectionsEquiv_restrict A.nonempty B.nonempty hst x, restrict_twice, restrict_twice]

theorem reduce_natural (h : B.closed ≤ A.closed) (x : A.E) :
    closedRes A B h (algebraMap A.E A.C x) = algebraMap B.E B.C (thickRes A B h x) := by
  apply B.closedValue.injective
  rw [closedRes_value, ← principalReduction_section A.vertices A.nonempty A.denominator x,
    ← principalReduction_section B.vertices B.nonempty B.denominator (thickRes A B h x), thickRes_value]
  exact (CycleQ2ChartSectionPullback.restriction_square closedFiber (thick_le A B h)
    (preimage_thickPrincipal _ _ _).ge h (preimage_thickPrincipal _ _ _).ge (A.thickValue x)).symm

abbrev split (a : Vertex) (ha : a ∈ A.vertices) : A.C →ₐ[ℂ] A.E :=
  localizedSplit (epsilonKernelEquiv A.vertices) A.denominator
    (projectiveSplittingAlgHom A.vertices a.1 ⟨a.2,ha⟩) (projectiveSplittingAlgHom_reduction _ _ _)

theorem split_reduces (a : Vertex) (ha : a ∈ A.vertices) (x : A.C) :
    algebraMap A.E A.C (A.split a ha x) = x :=
  localizedSplit_reduction _ _ _ _ _

theorem split_natural (h : B.closed ≤ A.closed) (hst : A.vertices ⊆ B.vertices)
    (a : Vertex) (ha : a ∈ A.vertices) (x : A.C) :
    thickRes A B h (A.split a ha x) = B.split a (hst ha) (closedRes A B h x) := by
  have he : (thickRes A B h).comp (A.split a ha).toRingHom =
      (B.split a (hst ha)).toRingHom.comp (closedRes A B h) := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (nativeReduction _ A.denominator))
    apply RingHom.ext
    intro y
    change thickRes A B h (A.split a ha (algebraMap (ClosedRing A.vertices) A.C y)) =
      B.split a (hst ha) (closedRes A B h (algebraMap (ClosedRing A.vertices) A.C y))
    rw [localizedSplit_base, thickRes_base A B h hst, closedRes_base A B h hst, localizedSplit_base]
    exact congrArg (algebraMap (ThickRing B.vertices) B.E) (projectiveSplittingAlgHom_restrict hst a.1 ⟨a.2,ha⟩ y)
  exact RingHom.congr_fun he x

theorem epsilon_one : epsilon A.kernelEquiv (1 : A.C) =
    algebraMap (ThickRing A.vertices) A.E (nativeEpsilon A.vertices) := by
  have he := localizedKernelEquiv_base (ThickRing A.vertices) (ClosedRing A.vertices) (epsilonKernelEquiv A.vertices)
    A.denominator (1 : ClosedRing A.vertices)
  rw [map_one] at he
  refine he.trans (congrArg _ ?_)
  change epsilonCoefficient A.vertices 1 = _
  have h := epsilonCoefficient_of_reduction A.vertices 1
  simpa only [map_one, mul_one] using h

theorem epsilon_natural (h : B.closed ≤ A.closed) (hst : A.vertices ⊆ B.vertices)
    (a : Vertex) (ha : a ∈ A.vertices) (x : A.C) :
    thickRes A B h (epsilon A.kernelEquiv x) = epsilon B.kernelEquiv (closedRes A B h x) := by
  have hε : thickRes A B h (epsilon A.kernelEquiv (1 : A.C)) = epsilon B.kernelEquiv (1 : B.C) := by
    rw [epsilon_one, epsilon_one, thickRes_base A B h hst, thickRestriction_epsilon]
  have l := mul_epsilon A.kernelEquiv (A.split a ha x) 1
  have r := mul_epsilon B.kernelEquiv (B.split a (hst ha) (closedRes A B h x)) 1
  rw [split_reduces, mul_one] at l r
  rw [← l, map_mul, hε, split_natural A B h hst]
  exact r

abbrev normalizedEdge (a : Vertex) (ha : a ∈ A.vertices) (u : A.Eˣ) :=
  unitCorrection A.kernelEquiv (A.split a ha) (A.split_reduces a ha) u

theorem normalizedEdge_restrict (h : B.closed ≤ A.closed) (hst : A.vertices ⊆ B.vertices)
    (a : Vertex) (ha : a ∈ A.vertices) (u : A.Eˣ) :
    closedRes A B h (A.normalizedEdge a ha u) = B.normalizedEdge a (hst ha)
      (Units.map (thickRes A B h).toMonoidHom u) :=
  unitCorrection_natural A.kernelEquiv (A.split a ha) (A.split_reduces a ha)
    B.kernelEquiv (B.split a (hst ha)) (B.split_reduces a (hst ha))
    (thickRes A B h) (closedRes A B h) (reduce_natural A B h) (epsilon_natural A B h hst a ha)
    (split_natural A B h hst a ha) u

end Chart
end CycleQ2LiteralMovingPivotCorrection
end

#print axioms CycleQ2LiteralMovingPivotCorrection.Chart.split_natural
#print axioms CycleQ2LiteralMovingPivotCorrection.Chart.normalizedEdge_restrict
