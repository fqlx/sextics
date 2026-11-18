import Proposal.GeometricGenericWeightedField
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.RingTheory.Kaehler.Basic

/-!
# Relative differentials of the weighted pencil field

The affine sextic equation determines the differential of its normal coordinate.
Consequently the differentials of the other three affine coordinates form a basis
over the weighted function field with both pencil parameters fixed.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2GenericWeightedDifferentials

open MvPolynomial CycleQ2IncidenceNormalForm CycleQ2GenericSpecialization
  CycleQ2GenericPencilLift CycleQ2GenericWeightedCoordinates CycleQ2GenericWeightedPencilEquation
  CycleQ2GenericWeightedField
open scoped BigOperators

variable (c : FullInvariantIndex 6 → ℂ) (hc : endpointDifference c ≠ 0)

private abbrev d := endpointDirection c hc
private abbrev W := field (d c hc)
private abbrev L := parameterField (d c hc)

private def point (i : Fin 5) : W c hc :=
  ⟨weightedPoint i, coordinate_mem _ i⟩

private theorem eval_to_ambient (p : MvPolynomial (Fin 5) (L c hc)) :
    (algebraMap (W c hc) RF) (eval₂Hom (algebraMap (L c hc) (W c hc)) (point c hc) p) =
      eval weightedPoint (MvPolynomial.map
        ((algebraMap (W c hc) RF).comp (algebraMap (L c hc) (W c hc))) p) := by
  rw [MvPolynomial.map_eval₂Hom, MvPolynomial.eval_map]
  rfl

private theorem normal_eq_zero (D : Derivation (L c hc) (W c hc) (W c hc))
    (hfree : ∀ j, D (coordinate (d c hc) j) = 0) : D (point c hc 1) = 0 := by
  classical
  obtain ⟨P, hP⟩ := equation_from_parameterField (d c hc) (endpointDifference c)
  let f := algebraMap (L c hc) (W c hc)
  have h₀ : eval₂Hom f (point c hc) P = 0 := (algebraMap (W c hc) RF).injective <| by
    rw [map_zero, eval_to_ambient, hP, endpoint_equation]
  have hn : eval₂Hom f (point c hc) (pderiv 1 P) ≠ 0 := by
    intro h
    apply endpoint_normal_ne_zero c hc
    rw [← hP, pderiv_map, ← eval_to_ambient, h, map_zero]
  have hd := CycleQ2GenericWeightedChainRule.eval_chain_rule (D.restrictScalars ℂ) f
    (point c hc) D.map_algebraMap P
  change D (eval₂Hom f (point c hc) P) =
    ∑ i, eval₂Hom f (point c hc) (pderiv i P) * D (point c hc i) at hd
  have hrest (i : Fin 5) (hi : i ≠ 1) : D (point c hc i) = 0 := by
    fin_cases i
    · exact D.map_one_eq_zero
    · exact (hi rfl).elim
    · exact hfree 0
    · exact hfree 1
    · exact hfree 2
  rw [h₀, map_zero, Finset.sum_eq_single (1 : Fin 5)
    (fun i _ hi => by rw [hrest i hi, mul_zero]) (by simp)] at hd
  exact (mul_eq_zero.mp hd.symm).resolve_left hn

/-- A relative derivation on the weighted field is determined by the three free coordinates. -/
theorem derivation_eq_zero (D : Derivation (L c hc) (W c hc) (W c hc))
    (hfree : ∀ j, D (coordinate (d c hc) j) = 0) : D = 0 := by
  have hnormal := normal_eq_zero c hc D hfree
  have hτ : D (⟨parameter (d c hc), parameter_mem _⟩ : W c hc) = 0 :=
    D.map_algebraMap (⟨_, IntermediateField.subset_adjoin _ _ (Set.mem_insert _ _)⟩ : L c hc)
  have hl : D (⟨lambda, lambda_mem _⟩ : W c hc) = 0 :=
    D.map_algebraMap (⟨_, IntermediateField.subset_adjoin _ _
      (Set.mem_insert_of_mem _ (Set.mem_singleton _))⟩ : L c hc)
  apply Derivation.ext
  intro a
  change D a = 0
  refine IntermediateField.adjoin_induction ℂ (p := fun x hx => D (⟨x, hx⟩ : W c hc) = 0)
    ?_ ?_ ?_ ?_ ?_ a.property
  · rintro _ (rfl | rfl | ⟨i, rfl⟩)
    · exact hτ
    · exact hl
    · fin_cases i
      · exact D.map_one_eq_zero
      · exact hnormal
      · exact hfree 0
      · exact hfree 1
      · exact hfree 2
  · intro b
    exact (D.restrictScalars ℂ).map_algebraMap b
  · intro x y hx hy hDx hDy
    change D ((⟨x, hx⟩ : W c hc) + ⟨y, hy⟩) = 0
    rw [map_add, hDx, hDy, add_zero]
  · intro x hx hDx
    change D (⟨x, hx⟩ : W c hc)⁻¹ = 0
    rw [Derivation.leibniz_inv, hDx, smul_zero]
  · intro x y hx hy hDx hDy
    change D ((⟨x, hx⟩ : W c hc) * ⟨y, hy⟩) = 0
    rw [Derivation.leibniz, hDx, hDy, smul_zero, smul_zero, add_zero]

private abbrev dx (i : Fin 3) : Ω[W c hc⁄L c hc] :=
  KaehlerDifferential.D (L c hc) (W c hc) (coordinate (d c hc) i)

private theorem dual_coordinates (i j : Fin 3) :
    (parameterDeriv c hc i).liftKaehlerDifferential (dx c hc j) = if i = j then 1 else 0 :=
  (Derivation.liftKaehlerDifferential_comp_D _ _).trans (parameterDeriv_coordinate c hc i j)

private theorem independent : LinearIndependent (W c hc) (dx c hc) := by
  classical
  apply Fintype.linearIndependent_iff.mpr
  intro g hg j
  have h := congrArg ((parameterDeriv c hc j).liftKaehlerDifferential) hg
  simp only [map_sum, map_smul, dual_coordinates, map_zero, smul_eq_mul, mul_ite, mul_one, mul_zero] at h
  simpa using h

theorem span_coordinate_differentials : Submodule.span (W c hc) (Set.range (dx c hc)) = ⊤ := by
  apply Submodule.dualAnnihilator_eq_bot_iff.mp
  apply le_antisymm _ bot_le
  intro l hl
  change l = 0
  apply Derivation.liftKaehlerDifferential_unique
  have he := derivation_eq_zero c hc (l.compDer (KaehlerDifferential.D (L c hc) (W c hc)))
    (fun j => (Submodule.mem_dualAnnihilator l).mp hl _ (Submodule.subset_span ⟨j, rfl⟩))
  exact he

/-- The differentials of the two free weight-one coordinates and the square coordinate. -/
def coordinateBasis : Module.Basis (Fin 3) (W c hc) Ω[W c hc⁄L c hc] :=
  Module.Basis.mk (independent c hc) (span_coordinate_differentials c hc).ge

@[simp] theorem coordinateBasis_apply (i : Fin 3) : coordinateBasis c hc i =
    KaehlerDifferential.D (L c hc) (W c hc) (coordinate (d c hc) i) :=
  Module.Basis.mk_apply _ _ _

/-- Differentiating a weighted rational function in this basis computes its three actual
relative partial derivatives. -/
theorem coordinateBasis_repr_D (x : W c hc) (j : Fin 3) :
    (coordinateBasis c hc).repr (KaehlerDifferential.D (L c hc) (W c hc) x) j =
      parameterDeriv c hc j x := by
  classical
  have h : (coordinateBasis c hc).coord j = (parameterDeriv c hc j).liftKaehlerDifferential := by
    apply (coordinateBasis c hc).ext
    intro i
    rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply]
    rw [coordinateBasis_apply]
    change (if i = j then 1 else 0) = (parameterDeriv c hc j).liftKaehlerDifferential (dx c hc i)
    rw [dual_coordinates]
    simp only [eq_comm]
  change (coordinateBasis c hc).coord j _ = _
  rw [h, Derivation.liftKaehlerDifferential_comp_D]

end CycleQ2GenericWeightedDifferentials
end

#print axioms CycleQ2GenericWeightedDifferentials.coordinateBasis
#print axioms CycleQ2GenericWeightedDifferentials.coordinateBasis_repr_D
