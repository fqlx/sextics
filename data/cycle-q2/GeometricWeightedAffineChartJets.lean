import Proposal.GeometricMonicWeightedAffineEquation
import Mathlib.Algebra.MvPolynomial.PDeriv

/-!
# Evaluation and normal jets on the affine weighted chart

Setting the first coordinate to one commutes with every partial derivative
in the other four coordinates. This identifies affine iterated normal jets
with the corresponding homogeneous-coordinate jets.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section

namespace CycleQ2WeightedAffineChartJets

open MvPolynomial
open CycleQ2MonicWeightedAffineEquation (chart)

variable {R K : Type} [CommRing R] [CommRing K]

theorem eval_chart (f : R →+* K) (x : Fin 4 → K) (p : MvPolynomial (Fin 5) R) :
    eval₂Hom f x (chart p) = eval₂Hom f (Fin.cases 1 x) p := by
  have h : (eval₂Hom f x).comp chart.toRingHom = eval₂Hom f (Fin.cases 1 x) := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [chart]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · simp [chart]
      · simp [chart]
  exact RingHom.congr_fun h p

theorem map_chart (f : R →+* K) (p : MvPolynomial (Fin 5) R) :
    MvPolynomial.map f (chart p) = chart (MvPolynomial.map f p) := by
  have h : (MvPolynomial.map f).comp chart.toRingHom =
      chart.toRingHom.comp (MvPolynomial.map f) := by
    apply MvPolynomial.ringHom_ext
    · intro a
      simp [chart]
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i <;> simp [chart]
  exact RingHom.congr_fun h p

private theorem pderiv_chart_X (i : Fin 4) (k : Fin 5) :
    pderiv i (chart (R := R) (X k)) = chart (pderiv i.succ (X k)) := by
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [chart, pderiv_X_of_ne (Ne.symm (Fin.succ_ne_zero i))]
  · by_cases h : j = i
    · subst j
      simp [chart]
    · simp [chart, pderiv_X_of_ne h, pderiv_X_of_ne ((Fin.succ_injective _).ne h)]

theorem pderiv_chart (i : Fin 4) (p : MvPolynomial (Fin 5) R) :
    pderiv i (chart p) = chart (pderiv i.succ p) := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [chart]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    simp only [map_mul, pderiv_mul, pderiv_chart_X, hp, map_add]

theorem iterate_pderiv_chart (i : Fin 4) (n : ℕ) (p : MvPolynomial (Fin 5) R) :
    (pderiv i)^[n] (chart p) = chart ((pderiv i.succ)^[n] p) := by
  induction n with
  | zero => rfl
  | succ n ih => rw [Function.iterate_succ_apply', ih, pderiv_chart, Function.iterate_succ_apply']

theorem eval_rename_succ (f : R →+* K) (x : Fin 4 → K) (p : MvPolynomial (Fin 4) R) :
    eval₂Hom f (Fin.cases 1 x) (rename Fin.succ p) = eval₂Hom f x p := by
  exact eval₂Hom_rename _ _ _ _

end CycleQ2WeightedAffineChartJets

end

#print axioms CycleQ2WeightedAffineChartJets.eval_chart
#print axioms CycleQ2WeightedAffineChartJets.iterate_pderiv_chart
