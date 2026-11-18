import Proposal.GeometricHodgeEulerSequence
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Determinant of the three consecutive Fermat normal-lift differences

In the first weight-one chart the pivot-zero component is removed by the
weighted Euler vector. Consecutive differences of the four one-component
normal lifts are evaluated on the ordered free coordinates x₂, x₃, w of
the x₁ derivative frame. Their determinant, times the inverse x₁ partial
from the residue, is the product of the three polynomial directions,
the radial w entry, and all four inverse partials.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeFermatYukawaDeterminant

open CycleQ2HodgeEuler (normalize)
open scoped Matrix

variable {A : Type*} [CommRing A]

/-- The j-th Fermat lift has a single component in the homogeneous frame. -/
def lift (d : Fin 4 → A) (j : Fin 4) (p : A) (a : Fin 5) : A :=
  if a = j.castSucc then p * d j else 0

def velocity (r : Fin 5 → A) (d : Fin 4 → A) (j : Fin 4) (p : A) : Fin 4 → A :=
  normalize (0 : Fin 5) r (lift d j p)

/-- Ordered values on x₂, x₃ and w, after omitting the ambient anchor x₀
and the derivative pivot x₁. -/
def row (r : Fin 5 → A) (d : Fin 4 → A) (j k : Fin 4) (p : A) (a : Fin 3) : A :=
  (velocity r d k p - velocity r d j p) ((0 : Fin 4).succAbove a)

def matrix (r : Fin 5 → A) (d : Fin 4 → A) (p q s : A) : Matrix (Fin 3) (Fin 3) A :=
  ![row r d 0 1 p, row r d 1 2 q, row r d 2 3 s]

theorem determinant (r : Fin 5 → A) (d : Fin 4 → A) (p q s : A) :
    (matrix r d p q s).det = (p*q*s) * r 4 * d 0 * d 2 * d 3 := by
  rw [Matrix.det_fin_three]
  simp only [matrix, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    row, velocity, normalize, LinearMap.coe_mk, AddHom.coe_mk, Pi.sub_apply, lift]
  norm_num [Fin.succAbove, Fin.ext_iff] <;> ring

theorem residue_evaluation (r : Fin 5 → A) (d : Fin 4 → A) (p q s w : A) (hw : r 4 = 2*w) :
    d 1 * (matrix r d p q s).det = 2 * (p*q*s) * w * ∏ j, d j := by
  rw [determinant, hw]
  rw [Fin.prod_univ_four]
  ring

end CycleQ2HodgeFermatYukawaDeterminant
end

#print axioms CycleQ2HodgeFermatYukawaDeterminant.residue_evaluation
