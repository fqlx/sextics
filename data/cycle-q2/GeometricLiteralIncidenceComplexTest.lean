import Proposal.GeometricLiteralIncidenceRelativeSpread
import Proposal.GeometricLiteralIncidenceNormalizedSlice
import Proposal.GeometricFiniteEtaleParameterPoint

/-!
# Complex points meeting a coefficient open and an open trace condition

Every nonempty open of the relative monic time family has complex points over
each nonempty Zariski open in the full coefficient space. In particular, a
regular function invertible at one marked point remains invertible at some
complex point above every such coefficient open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralIncidenceComplexTest

open CategoryTheory AlgebraicGeometry CycleQ2FiniteEtaleParameterPoint
  CycleQ2IncidenceEtaleParameter CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2LiteralIncidenceNormalizedSlice

private theorem complex_point_in {X : Scheme} (f : X ⟶ Spec (CommRingCat.of ℂ))
    [LocallyOfFiniteType f] (W : X.Opens) (hW : (W : Set X).Nonempty) :
    ∃ s : Spec (CommRingCat.of ℂ) ⟶ X, s ≫ f = 𝟙 _ ∧ s default ∈ W := by
  obtain ⟨x, hx, _, hf, _⟩ :=
    exists_finite_etale_closedPoint_in f (W : Set X) hW W.isOpen.isLocallyClosed
  let _ : Algebra ℂ (X.residueField x) := (pointFieldMap f x).hom.toAlgebra
  let _ : Module.Finite ℂ (X.residueField x) := hf
  have hbij : Function.Bijective (pointFieldMap f x).hom :=
    IsAlgClosed.algebraMap_bijective_of_isIntegral (k := ℂ)
  let e := (RingEquiv.ofBijective (pointFieldMap f x).hom hbij).toCommRingCatIso
  refine ⟨Spec.map e.inv ≫ X.fromSpecResidueField x, ?_, ?_⟩
  · rw [Category.assoc, ← pointFieldMap_spec, ← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map e.hom_inv_id
  · have he : (Spec.map e.inv ≫ X.fromSpecResidueField x) default = x :=
      Scheme.fromSpecResidueField_apply (X := X) x ((Spec.map e.inv) default)
    rw [he]
    exact hx

/-- A complex point in the actual monic time family satisfies both open conditions. -/
theorem complex_point_over_open (V : parameterScheme.Opens) (W : (Time toRaw V).Opens)
    (hW : (W : Set (Time toRaw V)).Nonempty) (U : monicBase.Opens)
    (hU : (U : Set monicBase).Nonempty) :
    ∃ s : Spec (CommRingCat.of ℂ) ⟶ Time toRaw V,
      s ≫ timeMap toRaw V ≫ toComplex = 𝟙 _ ∧ s default ∈ W ∧ timeMap toRaw V (s default) ∈ U := by
  have : IrreducibleSpace monicBase :=
    inferInstanceAs (IrreducibleSpace (Spec (CommRingCat.of MonicRing)))
  have := timeMap_smooth toRaw V
  have : Smooth (timeMap toRaw V) := SmoothOfRelativeDimension.smooth 1 _
  have : LocallyOfFiniteType toComplex := by
    apply (HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)).mpr
    exact RingHom.finiteType_algebraMap.mpr (inferInstance : Algebra.FiniteType ℂ MonicRing)
  obtain ⟨x, hx, hxU⟩ := timeOpen_meets_coefficients toRaw V W hW U hU
  obtain ⟨s, hs, hsW⟩ := complex_point_in (timeMap toRaw V ≫ toComplex)
    (W ⊓ timeMap toRaw V ⁻¹ᵁ U) ⟨x, hx, hxU⟩
  exact ⟨s, hs, hsW.1, hsW.2⟩

/-- A regular test invertible at a marked point stays invertible above a prescribed
nonempty coefficient open, at a genuine complex point. -/
theorem regular_test_over_open (V : parameterScheme.Opens) (W : (Time toRaw V).Opens)
    (a : Γ(Time toRaw V, W)) (x : Time toRaw V) (hx : x ∈ (Time toRaw V).basicOpen a)
    (U : monicBase.Opens) (hU : (U : Set monicBase).Nonempty) :
    ∃ s : Spec (CommRingCat.of ℂ) ⟶ Time toRaw V,
      s ≫ timeMap toRaw V ≫ toComplex = 𝟙 _ ∧
      s default ∈ (Time toRaw V).basicOpen a ∧ timeMap toRaw V (s default) ∈ U :=
  complex_point_over_open V _ ⟨x, hx⟩ U hU

end CycleQ2LiteralIncidenceComplexTest
end

#print axioms CycleQ2LiteralIncidenceComplexTest.regular_test_over_open
