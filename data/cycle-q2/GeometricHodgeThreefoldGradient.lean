import Proposal.GeometricHodgeEuler

/-!
# The four derivatives generate the unit ideal on each affine sextic chart

The homogeneous gradient contains a power of the chosen degree-one
coordinate on the gradient minor open. This power becomes one on its
normalized affine chart. The Euler relation eliminates the omitted
partial since the corresponding radial coordinate is one.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricHodgeThreefold

open MvPolynomial CycleQ2GenericSexticGradient CycleQ2HodgeEuler

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)
  (hg : IsUnit (φ gradientOpen)) (i : Fin 4)

include hg

theorem chartGradient_span :
    Ideal.span (Set.range (fun j : Fin 4 => chartMap φ i (pderiv j (F φ i)))) = ⊤ := by
  let J := Ideal.span (Set.range (fun j : Fin 4 => chartMap φ i (pderiv j (F φ i))))
  have hret (j : Fin 4) : conePartial φ i (i.castSucc.succAbove j) ∈ J := by
    rw [partial_succAbove]
    exact Ideal.subset_span (Set.mem_range_self j)
  have he := radial_equation φ i
  rw [Fin.sum_univ_succAbove _ i.castSucc, radial_self, mul_one] at he
  have hall (j : Fin 5) : conePartial φ i j ∈ J := by
    refine Fin.succAboveCases i.castSucc ?_ hret j
    rw [eq_neg_of_add_eq_zero_left he]
    exact J.neg_mem (J.sum_mem fun k _ => J.mul_mem_right _ (hret k))
  let ρ := (chartMap φ i).toRingHom.comp (dehom (R := R) i).toRingHom
  have hI : CycleQ2HomogeneousIdealArithmetic.generatorIdeal
      (fun j => MvPolynomial.map φ (generators j)) ≤ J.comap ρ := by
    apply Ideal.span_le.mpr
    rintro _ ⟨j, rfl⟩
    change ρ (MvPolynomial.map φ (X j * pderiv j universalF)) ∈ J
    rw [map_mul, map_mul, ← pderiv_map]
    exact J.mul_mem_left _ (hall j)
  apply J.eq_top_iff_one.mpr
  have h := hI (coordinate_power_mem φ hg i.castSucc)
  change ρ ((X i.castSucc)^coordinatePower i.castSucc) ∈ J at h
  simpa [ρ] using h

theorem conePartial_span : Ideal.span (Set.range (conePartial φ i)) = ⊤ := by
  apply top_le_iff.mp
  rw [← chartGradient_span φ hg i]
  apply Ideal.span_mono
  rintro _ ⟨j, rfl⟩
  exact ⟨i.castSucc.succAbove j, partial_succAbove φ i j⟩

end CycleQ2GeometricHodgeThreefold
end

#print axioms CycleQ2GeometricHodgeThreefold.chartGradient_span
