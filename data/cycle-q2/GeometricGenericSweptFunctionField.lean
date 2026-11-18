import Proposal.GeometricGenericSweptExtSupport
import Proposal.GeometricLiteralSweptDimensionUpper
import Proposal.GeometricAffineChartDimensionBound
import Proposal.GeometricMonicGenericAmbientChart
import Proposal.GeometricMonicGenericAmbientDomain

/-!
# The generic swept correspondence away from the function point

The original relative surface sweeps out a nonempty closed scheme of
dimension at most two over the monic coefficient function field. The
three-dimensional first affine chart therefore has a nonempty
distinguished open outside that scheme. Its fraction-field point factors
through this complement, where the relative two-form coefficient vanishes.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GenericSweptFunctionField

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralGenericSweptFamily CycleQ2GenericSweptExtSupport
  CycleQ2LiteralIncidenceRelativeCylinder CycleQ2LiteralIncidenceRelativeSpread
  CycleQ2MonicGenericAmbientChart CycleQ2IncidenceSeedFiberCover

open CycleQ2IncidenceEtaleParameter (parameterScheme)

abbrev chartField := FractionRing genericChartRing

def functionPoint : Spec (CommRingCat.of chartField) ⟶ Threefold :=
  Spec.map (CommRingCat.ofHom (algebraMap genericChartRing chartField)) ≫ chartInclusion

variable {V : parameterScheme.Opens} {t : Fin 3 → ℂ}

private theorem chart_not_contained (hd : topologicalKrullDim (swept V t) ≤ 2) :
    ¬ Set.range chartInclusion ⊆ Set.range (inclusion V t) := by
  intro h
  have h₁ := IsHomeomorph.topologicalKrullDim_eq _
    chartInclusion.isOpenEmbedding.isEmbedding.toHomeomorph.isHomeomorph
  have h₂ := IsHomeomorph.topologicalKrullDim_eq _
    (inclusion V t).isClosedEmbedding.isEmbedding.toHomeomorph.isHomeomorph
  have h₃ := (Topology.IsEmbedding.inclusion h).isInducing.topologicalKrullDim_le
  have ha := CycleQ2MonicGenericAmbientChart.chart_dimension
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim] at ha
  exact (by decide : ¬ (3 : WithBot ℕ∞) ≤ 2) (ha.trans (h₁.le.trans (h₃.trans (h₂.ge.trans hd))))

/-- A genuine nonzero denominator in the first chart, outside the swept surface. -/
theorem exists_basic_open (hd : topologicalKrullDim (swept V t) ≤ 2) :
    ∃ s : genericChartRing, s ≠ 0 ∧
      PrimeSpectrum.basicOpen s ≤ chartInclusion ⁻¹ᵁ complement V t := by
  obtain ⟨_, ⟨x,rfl⟩, hx⟩ := Set.not_subset.mp (chart_not_contained hd)
  let W := chartInclusion ⁻¹ᵁ complement V t
  have hx' : x ∈ W := hx
  obtain ⟨_, ⟨s,rfl⟩, hs, hsub⟩ := PrimeSpectrum.isTopologicalBasis_basic_opens.isOpen_iff.mp
    W.isOpen x hx'
  refine ⟨s, ?_, hsub⟩
  intro e
  exact (PrimeSpectrum.mem_basicOpen s x).mp hs (by rw [e]; exact x.asIdeal.zero_mem)

theorem functionPoint_mem_complement (hd : topologicalKrullDim (swept V t) ≤ 2)
    (x : Spec (CommRingCat.of chartField)) : functionPoint x ∈ complement V t := by
  obtain ⟨s, hs, hle⟩ := exists_basic_open hd
  apply hle
  apply (PrimeSpectrum.mem_basicOpen s _).mpr
  change algebraMap genericChartRing chartField s ∉ x.asIdeal
  have hne : algebraMap genericChartRing chartField s ≠ 0 := fun h =>
    hs (IsFractionRing.injective genericChartRing chartField (h.trans (map_zero _).symm))
  exact fun h => x.isPrime.ne_top (x.asIdeal.eq_top_of_isUnit_mem h hne.isUnit)

/-- The function-field point factors through the complement on the ambient scheme. -/
def functionPointLift (hd : topologicalKrullDim (swept V t) ≤ 2) :
    Spec (CommRingCat.of chartField) ⟶ (complement V t).toScheme :=
  IsOpenImmersion.lift (complement V t).ι functionPoint <| by
    rintro _ ⟨x,rfl⟩
    exact ⟨⟨_, functionPoint_mem_complement hd x⟩,rfl⟩

@[reassoc (attr := simp)] theorem functionPointLift_fac
    (hd : topologicalKrullDim (swept V t) ≤ 2) :
    functionPointLift hd ≫ (complement V t).ι = functionPoint :=
  IsOpenImmersion.lift_fac _ _ _

/-- The actual generic two-form direct image has zero module pullback to the first chart's
function field. -/
theorem directImage_at_functionPoint (hd : topologicalKrullDim (swept V t) ≤ 2) :
    IsZero ((Scheme.Modules.pullback functionPoint).obj (directImage V t)) := by
  have h := ((Scheme.Modules.restrictFunctorIsoPullback (complement V t).ι).app
    (directImage V t)).isZero_iff.mp (directImage_off V t)
  rw [← functionPointLift_fac hd]
  apply ((Scheme.Modules.pullbackComp (functionPointLift hd) (complement V t).ι).app
    (directImage V t)).isZero_iff.mp
  exact (Scheme.Modules.pullback (functionPointLift hd)).map_isZero h

/-- Pullback to the function field kills the specific relative Kähler two-form map
whose precomposition defines the supported Yoneda class. -/
theorem coefficientsMap_at_functionPoint (hd : topologicalKrullDim (swept V t) ≤ 2) :
    (Scheme.Modules.pullback functionPoint).map (coefficientsMap V t) = 0 :=
  (directImage_at_functionPoint hd).eq_of_tgt _ _

theorem exists_supported_generic_family (t : Fin 3 → ℂ) (hi : AlgebraicIndependent ℚ t) :
    ∃ (V : parameterScheme.Opens) (_ : seedBasePoint ∈ V),
      Nonempty (swept V t) ∧ IsProper (inclusion V t ≫ structureMap) ∧
      topologicalKrullDim (swept V t) ≤ 2 ∧
      (∃ s : genericChartRing, s ≠ 0 ∧ PrimeSpectrum.basicOpen s ≤ chartInclusion ⁻¹ᵁ complement V t) ∧
      IsZero ((Scheme.Modules.pullback functionPoint).obj (directImage V t)) := by
  obtain ⟨V,hV,h⟩ := CycleQ2LiteralSweptDimensionUpper.coefficient_surface t hi
  obtain ⟨hc,_,hb⟩ := h _ coefficient
  have hd := CycleQ2AffineChartDimensionBound.topologicalKrullDim_le (swept V t) 2
    (fun W hW => Ring.krullDimLE_iff.mp (hb W hW))
  let := CycleQ2LiteralRelativeAmbientProper.ambient_proper coefficient
  exact ⟨V, hV, generic_support_nonempty V hV t hc, inferInstance, hd,
    exists_basic_open hd, directImage_at_functionPoint hd⟩

end CycleQ2GenericSweptFunctionField
end

#print axioms CycleQ2GenericSweptFunctionField.exists_supported_generic_family
