import Proposal.GeometricLiteralTimeCurveDimension
import Proposal.GeometricLiteralTimeCurveLocalNormal
import Mathlib.AlgebraicGeometry.FunctionField

/-!
# Local rings of the normalized time branch

For an affine integral parameter open, the sections of every nonempty
affine chart of the relative normalization are integrally closed. The
dimension bound makes those charts Dedekind domains, so the stalks of
the proper base are fields or discrete valuation rings at all points.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeNormalizationRegular
open CategoryTheory AlgebraicGeometry TopologicalSpace CycleQ2LiteralIncidenceTimeCurve
  CycleQ2LiteralTimeCurveCompletion CycleQ2LiteralTimeCurveNormalization

variable (U : Curve.Opens) [IsAffine U.toScheme] [AlgebraicGeometry.IsIntegral U.toScheme]
omit [AlgebraicGeometry.IsIntegral U.toScheme] in
private theorem preimage_affine {V : (Completion U).Opens} (hV : IsAffineOpen V) :
    IsAffineOpen (inclusion U ⁻¹ᵁ V) := by
  rw [← (inclusion U).isAffineOpen_iff_of_isOpenImmersion,
    (inclusion U).image_preimage_eq_opensRange_inf]
  let p := structureMap U
  let : IsProper p := inferInstanceAs (IsProper (structureMap U))
  exact (isAffineHom_diagonal_iff (f := p)).mp inferInstance ⊤ (isAffineOpen_top _)
    _ (by simp) _ (by simp) (isAffineOpen_opensRange (inclusion U)) hV

theorem preimage_dedekind
    {V : (Completion U).Opens} (hV : IsAffineOpen V) (x : Normalization U)
    (hx : toCompletion U x ∈ V) :
    IsDedekindDomain Γ(Normalization U, toCompletion U ⁻¹ᵁ V) := by
  let j := inclusion U
  let W := j ⁻¹ᵁ V
  have : Nonempty W := by
    obtain ⟨z, hz⟩ := j.denseRange.exists_mem_open V.isOpen ⟨_, hx⟩
    exact ⟨⟨z, hz⟩⟩
  let A := Γ(Completion U, V)
  let H := Γ(U.toScheme, W)
  let : Algebra A H := (j.app V).hom.toAlgebra
  let : IsDomain H := inferInstanceAs (IsDomain Γ(U.toScheme, W))
  let : IsIntegrallyClosed H :=
    CycleQ2LiteralTimeCurveLocalNormal.affineOpen_isIntegrallyClosed_of_openImmersion U.ι W
      (preimage_affine U hV)
  let : IsIntegrallyClosed (integralClosure A H) :=
    IsIntegrallyClosed.of_isIntegrallyClosed_of_isIntegrallyClosedIn (integralClosure A H) H
  let T := toCompletion U ⁻¹ᵁ V
  let D := Γ(Normalization U,T)
  let e : D ≃+* integralClosure A H := (j.normalizationObjIso hV).commRingCatIsoToRingEquiv
  let : IsIntegrallyClosed D := IsIntegrallyClosed.of_equiv e.symm
  let : IsDomain D := e.injective.isDomain e.toRingHom
  let hT : IsAffineOpen T := hV.preimage (toCompletion U)
  let : IsLocallyNoetherian (Normalization U) := LocallyOfFiniteType.isLocallyNoetherian (toComplexPoint U)
  let : IsNoetherianRing D := IsLocallyNoetherian.component_noetherian ⟨T,hT⟩
  let : Ring.KrullDimLE 1 D := CycleQ2LiteralTimeCurveDimension.normalization_chart U hT
  exact { maximalOfPrime := fun h hp => (Ring.krullDimLE_one_iff_of_noZeroDivisors.mp
    (inferInstance : Ring.KrullDimLE 1 D) _ h hp) }

theorem stalk_dedekind
    (x : Normalization U) : IsDedekindDomain ((Normalization U).presheaf.stalk x) := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hx, _⟩ :=
    (Completion U).isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (toCompletion U x)) isOpen_univ
  let T := toCompletion U ⁻¹ᵁ V
  let hT : IsAffineOpen T := hV.preimage (toCompletion U)
  let z : T := ⟨x, hx⟩
  let p := (hT.primeIdealOf z).asIdeal
  let : Algebra Γ(Normalization U,T) ((Normalization U).presheaf.stalk x) :=
    TopCat.Presheaf.algebra_section_stalk (Normalization U).presheaf z
  let := hT.isLocalization_stalk z
  let : IsDedekindDomain Γ(Normalization U,T) := preimage_dedekind U hV x hx
  let : AlgebraicGeometry.IsIntegral (Normalization U) :=
    inferInstanceAs (AlgebraicGeometry.IsIntegral (inclusion U).normalization)
  exact IsLocalization.AtPrime.isDedekindDomain Γ(Normalization U,T) p ((Normalization U).presheaf.stalk x)

theorem stalk_field_or_dvr (x : Normalization U) :
    IsField ((Normalization U).presheaf.stalk x) ∨
      IsDiscreteValuationRing ((Normalization U).presheaf.stalk x) := by
  let D := (Normalization U).presheaf.stalk x
  let : IsDedekindDomain D := stalk_dedekind U x
  by_cases h : IsField D
  · exact Or.inl h
  · exact Or.inr (((IsDiscreteValuationRing.TFAE D h).out 2 0).mp (inferInstance : IsDedekindDomain D))

end CycleQ2LiteralTimeNormalizationRegular
end

#print axioms CycleQ2LiteralTimeNormalizationRegular.stalk_dedekind
#print axioms CycleQ2LiteralTimeNormalizationRegular.stalk_field_or_dvr
