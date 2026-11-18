import Proposal.ScratchWeightedDoublePoleCech
import Proposal.ScratchLogCofactor
import Proposal.ScratchLogInteriorAnti
import Proposal.ScratchLogIndexRealization

/-!
# The meromorphic Čech representative on Kähler forms

The three components of the reduced pole are actual exterior powers of the
cotangent module. The three overlap identities follow from the coordinate
array identities by differentiating the signed cofactors. The correcting
four- and three-forms exhibit the coboundary relating this representative
to twice the original cubic-pole rational five-form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogCofactorRealization

open CycleQ2LogarithmicDifferential (Form exteriorD coordDeriv partials_commute)
open CycleQ2LogCofactor (volume first second)
open CycleQ2LogInteriorAnti (interior_square interior_swap)
open CycleQ2LiteralThreefoldResidueContraction (interior)
open CycleQ2WeightedDoublePoleCech

variable {k K : Type} [CommRing k] [Field K] [Algebra k K]
variable (b : Module.Basis (Fin 5) K (KaehlerDifferential k K))

/-- A scalar times the ordered top form. -/
def top : K →ₗ[K] Form k K 5 := (LinearMap.id : K →ₗ[K] K).smulRight (volume b)

/-- Realization of a vector in the four-form cofactors of the ambient volume. -/
def flux : Flux (Fin 5) K →ₗ[K] Form k K 4 :=
  CycleQ2LogIndexRealization.vector (fun i => interior 4 (b.coord i) (volume b))

/-- Realization of a skew matrix in three-forms, using its strict upper triangle. -/
def biv : Biv (Fin 5) K →ₗ[K] Form k K 3 :=
  CycleQ2LogIndexRealization.matrix (fun i j => interior 3 (b.coord i)
    (interior 4 (b.coord j) (volume b)))

theorem flux_apply (v : Flux (Fin 5) K) :
    flux b v = ∑ i, v i • interior 4 (b.coord i) (volume b) := rfl

theorem biv_apply (v : Biv (Fin 5) K) :
    biv b v = ∑ i, ∑ j, if i < j then
      v i j • interior 3 (b.coord i) (interior 4 (b.coord j) (volume b)) else 0 := by
  change (∑ i, ∑ j, v i j • (if i < j then
    interior 3 (b.coord i) (interior 4 (b.coord j) (volume b)) else 0)) = _
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  by_cases h : i < j <;> simp [h]

theorem flux_oneIndex (i : Fin 5) (a : K) :
    flux b (oneIndex i a) = a • interior 4 (b.coord i) (volume b) :=
  CycleQ2LogIndexRealization.vector_single _ _ _

theorem biv_twoIndex (i j : Fin 5) (a : K) :
    biv b (twoIndex i j a) = a • interior 3 (b.coord i) (interior 4 (b.coord j) (volume b)) :=
  CycleQ2LogIndexRealization.matrix_skew_single _ (fun _ => interior_square _ _ _)
    (fun _ _ => interior_swap _ _ _ _) _ _ _

local notation "D" => coordDeriv b

theorem d_flux (v : Flux (Fin 5) K) :
    exteriorD b 4 (flux b v) = top b (topDerivative D v) := by
  change exteriorD b 4 (∑ i, v i • interior 4 (b.coord i) (volume b)) =
    (∑ i, D i (v i)) • volume b
  simp only [map_sum, first, Finset.sum_smul]

theorem d_biv_twoIndex (i j : Fin 5) (a : K) :
    exteriorD b 3 (biv b (twoIndex i j a)) = flux b (fluxDerivative D (twoIndex i j a)) := by
  rw [biv_twoIndex, second, fluxDerivative_twoIndex, map_sub, flux_oneIndex, flux_oneIndex]

theorem d_biv_face (F N : K) (i j l : Fin 5) :
    exteriorD b 3 (biv b (face D F N i j l)) = flux b (fluxDerivative D (face D F N i j l)) := by
  simp only [face, edgeCorrection, map_sub, map_add, map_neg, d_biv_twoIndex]

/-- On the ambient cone an exact frame realizes the three signed Čech equations
of the twice-reduced five-form. -/
theorem meromorphic_form_cocycle (x : Fin 5 → K) (hx : ∀ i, b i = KaehlerDifferential.D k K (x i))
    (F N : K) (i j l m : Fin 5) (hf : F ≠ 0)
    (hi : normal D F i ≠ 0) (hj : normal D F j ≠ 0) (hl : normal D F l ≠ 0) :
    exteriorD b 4 (flux b (edge D F N i j)) = top b (vertex D F N j) - top b (vertex D F N i) ∧
    exteriorD b 3 (biv b (face D F N i j l)) =
      -(flux b (edge D F N j l) - flux b (edge D F N i l) + flux b (edge D F N i j)) ∧
    biv b (face D F N j l m) - biv b (face D F N i l m) +
      biv b (face D F N i j m) - biv b (face D F N i j l) = 0 := by
  obtain ⟨h₁, h₂, h₃⟩ := simplePole_cocycle D F N (partials_commute b x hx) hf i j l m hi hj hl
  refine ⟨?_, ?_, ?_⟩
  · rw [d_flux, h₁, map_sub]
  · rw [d_biv_face, h₂, map_neg, map_add, map_sub]
  · simpa only [map_add, map_sub, map_zero] using congrArg (biv b) h₃

/-- The cohomology class is fixed by the displayed vertex and edge corrections. -/
theorem meromorphic_form_comparison (F N : K) (i j : Fin 5)
    (hf : F ≠ 0) (hi : normal D F i ≠ 0) (hj : normal D F j ≠ 0) :
    top b (vertex D F N i) = top b (2*N/F^3) - exteriorD b 4 (flux b (vertexCorrection D F N i)) ∧
    flux b (edge D F N i j) = flux b (vertexCorrection D F N i) -
      flux b (vertexCorrection D F N j) + exteriorD b 3 (biv b (edgeCorrection D F N i j)) := by
  constructor
  · rw [d_flux, vertex_comparison D F N i hf hi, map_sub]
  · rw [edge_comparison D F N i j hf hi hj, map_add, map_sub, edgeCorrection, d_biv_twoIndex]

end CycleQ2LogCofactorRealization
end
#print axioms CycleQ2LogCofactorRealization.meromorphic_form_cocycle
#print axioms CycleQ2LogCofactorRealization.meromorphic_form_comparison
