import Proposal.GeometricHodgeThreefoldCubicChart
import Mathlib.RingTheory.Ideal.HasGoingUp
import Mathlib.RingTheory.KrullDimension.Polynomial

/-!
# Dimension of the monic threefold charts

The cubic projection onto affine three-space is finite and its map of
coordinate rings is injective. Going up and incomparability therefore
identify the two Krull dimensions.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

namespace CycleQ2MonicGenericAmbientChartDimension

open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (vertexCoefficient)
open CycleQ2GeometricHodgeThreefoldCubic

private theorem integral_dimension (R S : Type*) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.IsIntegral R S] (inj : Function.Injective (algebraMap R S)) :
    ringKrullDim S = ringKrullDim R := by
  apply le_antisymm
  · exact Order.krullDim_le_of_strictMono (PrimeSpectrum.comap (algebraMap R S))
      (fun _ _ h => Ideal.IsIntegral.comap_lt_comap h)
  · change Order.krullDim (PrimeSpectrum R) ≤ _
    rw [Order.krullDim]
    apply iSup_le
    intro l
    obtain ⟨P, _, hP, heq⟩ := Ideal.exists_ideal_over_prime_of_isIntegral l.head.asIdeal
      (⊥ : Ideal S) (by simp [Ideal.comap_bot_of_injective _ inj])
    have : P.LiesOver l.head.asIdeal := ⟨heq.symm⟩
    obtain ⟨L, hlen, _, _⟩ := Ideal.exists_ltSeries_of_hasGoingUp l P
    rw [← hlen]
    exact Order.LTSeries.length_le_krullDim L

theorem chart_dimension_eq {K : Type} [Field K] (φ : CoeffRing →+* K) (i : Fin 4)
    (h : IsUnit (φ vertexCoefficient)) : ringKrullDim (CycleQ2HodgeEuler.chart φ i) = 3 := by
  rw [ringKrullDim_eq_of_ringEquiv (chartEquivAdjoinRoot φ i h).toRingEquiv]
  have hm := cubic_monic φ i h
  letI := hm.finite_adjoinRoot
  have hinj : Function.Injective (algebraMap (Base K) (AdjoinRoot (cubic φ i h))) := by
    rw [AdjoinRoot.algebraMap_eq]
    apply AdjoinRoot.of.injective_of_degree_ne_zero
    rw [Polynomial.degree_eq_natDegree hm.ne_zero, cubic_natDegree]
    decide
  rw [integral_dimension (Base K) _ hinj]
  have dim_field : ringKrullDim K = 0 := Order.krullDim_eq_zero_of_unique
  simp [Base, MvPolynomial.ringKrullDim_of_isNoetherianRing, Nat.card_eq_fintype_card, dim_field]

theorem chart_dimension {K : Type} [Field K] (φ : CoeffRing →+* K) (i : Fin 4)
    (h : IsUnit (φ vertexCoefficient)) : 3 ≤ ringKrullDim (CycleQ2HodgeEuler.chart φ i) :=
  (chart_dimension_eq φ i h).ge

end CycleQ2MonicGenericAmbientChartDimension

#print axioms CycleQ2MonicGenericAmbientChartDimension.chart_dimension_eq
#print axioms CycleQ2MonicGenericAmbientChartDimension.chart_dimension
