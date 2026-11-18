import Proposal.GeometricHodgeFermatTraceRows
import Proposal.GeometricHodgeTwistResidueCoefficient

/-!
# Laurent rows for numerators over powers of the four coordinate denominators

In the zeroth frame the other three exponents are shifted by the common
denominator power. The missing exponent is dictated by the homogeneous
degree of the cubic slot. Only slot two and the exponent (n,n,n) can
contribute to the top trace for a denominator of exponent n+1.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeTwistResidueRows
open MvPolynomial
open CycleQ2HodgeTwistCech (Exp Vertex)
open CycleQ2HodgeTopCech (TopSection trace)
open CycleQ2HodgeFermatTraceRows (term trace_term)
open CycleQ2HodgeTwistResidueCoefficient (exponent)

variable {R : Type} [CommRing R]

def tail (n : ℕ) (d : Fin 3 →₀ ℕ) (i : Fin 3) : ℤ := (d i : ℤ) - (n+1)

def row (n : ℕ) (j : Fin 3) (d : Fin 3 →₀ ℕ) : Exp :=
  Fin.cons (-(∑ i, tail n d i) - 2*(j.val : ℤ)) (tail n d)

theorem row_degree (n : ℕ) (j : Fin 3) (d : Fin 3 →₀ ℕ) :
    (∑ i, row n j d i) + 2*(j.val : ℤ) = 0 := by
  simp only [Fin.sum_univ_succ, row, Fin.cons_zero, Fin.cons_succ]
  omega

theorem row_top_iff (n : ℕ) (d : Fin 3 →₀ ℕ) :
    row n 2 d = (fun _ => (-1 : ℤ)) ↔ d = exponent n := by
  constructor
  · intro h
    ext i
    have he := congrFun h i.succ
    simp only [row, Fin.cons_succ, tail] at he
    change d i = n
    omega
  · rintro rfl
    have ht (i : Fin 3) : tail n (exponent n) i = -1 := by change (n : ℤ) - (n + 1) = -1; omega
    funext i
    refine Fin.cases ?_ (fun k => ?_) i
    · simp [row, ht, Fin.sum_univ_three]
    · exact ht k

def form (n : ℕ) (p : Fin 3 → MvPolynomial (Fin 3) R) : TopSection R 0 :=
  ∑ j, ∑ d ∈ (p j).support,
    term j (row n j d) (coeff d (p j)) (row_degree n j d)

theorem trace_form (n : ℕ) (p : Fin 3 → MvPolynomial (Fin 3) R) :
    trace (form n p) = coeff (exponent n) (p 2) := by
  classical
  rw [form, map_sum, Finset.sum_eq_single (2 : Fin 3)]
  · rw [map_sum, Finset.sum_eq_single (exponent n)]
    · simp only [trace_term, true_and, row_top_iff, if_pos rfl]
    · intro d _ hd
      simp [trace_term, row_top_iff, hd]
    · intro h; simp [trace_term, row_top_iff, notMem_support_iff.mp h]
  · intro j _ hj
    rw [map_sum]
    exact Finset.sum_eq_zero (fun d _ => by simp [trace_term, hj])
  · simp

end CycleQ2HodgeTwistResidueRows
end
#print axioms CycleQ2HodgeTwistResidueRows.trace_form
