import Proposal.GeometricHodgeFermatNormalLifts
import Proposal.GeometricHodgeEulerQuotientFrames

/-!
# The Fermat determinant in the actual projective chart

Read the four honest lifts through the normal morphism in a common
weight-one frame and remove their Euler component. The determinant of
the three successive differences on the free x₂, x₃, w coordinates,
divided by the x₁ partial, is a function of the actual threefold.
It equals the product of the three numerators times 2w and all four
inverse partials, on every open contained in the four coordinates.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeFermatYukawaRows

open AlgebraicGeometry CategoryTheory Limits
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEulerSheaf CycleQ2HodgeThreefoldTwist
open CycleQ2HodgeTwistRatios CycleQ2HodgeFermatNormalLifts
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2HodgeEulerQuotientFrames (euler)
open CycleQ2HodgeEuler (normalize)
open scoped Matrix

variable (V : (threefold ψ).Opens) (h : ∀ i : Fin 4, V ≤ U ψ i)

abbrev d (i : Fin 4) := inversePartial i V (h i) (h 0)
abbrev w := normalized ψ 0 (coord ψ 4) (coord_mem_grade ψ 4) V (h 0)
abbrev value (p : grade ψ 6) := normalized ψ 0 p.val p.property V (h 0)
abbrev radial := euler ψ 0 V (h 0)

theorem inverse_partial (i : Fin 4) :
    d V h i * normalized ψ 0 (partialValue ψ i.castSucc) (partial_mem ψ i.castSucc) V (h 0) = 1 := by
  let u := transition ψ 0 i V (h 0) (h i)
  have hh : normalized ψ 0 (partialValue ψ i.castSucc) (partial_mem ψ i.castSucc) V (h 0) =
      u.val ^ 5 * 6 := by
    have hn := normalized_change ψ 0 i (partialValue ψ i.castSucc) (partial_mem ψ i.castSucc) V (h 0) (h i)
    rw [self_partial] at hn
    simpa only [CycleQ2SeedFermatProj.geometricWeight_castSucc, Nat.reduceSub] using hn
  have hp : (u ^ (-5 : ℤ)).val * u.val ^ 5 = 1 := by
    have he : u ^ (-5 : ℤ) * u ^ (5 : ℤ) = 1 := by rw [← zpow_add]; norm_num
    exact congrArg Units.val he
  rw [hh]
  change (invSix V * (u ^ (-5 : ℤ)).val) * (u.val ^ 5 * 6) = 1
  calc
    _ = (6 * invSix V) * ((u ^ (-5 : ℤ)).val * u.val ^ 5) := by ring
    _ = 1 := by rw [six_invSix, hp, mul_one]

def read (j : Fin 4) (p : grade ψ 6) (a : Fin 5) : Γ(threefold ψ,V) :=
  chartFrame ψ (geometricWeight a) 0 V (h 0) ((Pi.π (pieces ψ) a).app V (lift j V (h j) p.val p.property))

def row (i j : Fin 4) (p : grade ψ 6) (k : Fin 3) : Γ(threefold ψ,V) :=
  (normalize (0 : Fin 5) (radial V h) (read V h j p - read V h i p)) ((0 : Fin 4).succAbove k)

theorem row_eq (i j : Fin 4) (p : grade ψ 6) :
    row V h i j p = CycleQ2HodgeFermatYukawaDeterminant.row (radial V h) (d V h) i j (value V h p) := by
  have hread (k : Fin 4) : read V h k p =
      CycleQ2HodgeFermatYukawaDeterminant.lift (d V h) k (value V h p) :=
    funext fun a => read_lift k V (h k) p.val p.property h a
  funext k
  unfold row
  rw [map_sub, hread, hread]
  rfl

def matrix (p q s : grade ψ 6) : Matrix (Fin 3) (Fin 3) Γ(threefold ψ,V) :=
  ![row V h 0 1 p, row V h 1 2 q, row V h 2 3 s]

theorem native_determinant (p q s : grade ψ 6) :
    d V h 1 * (matrix V h p q s).det =
      2 * (value V h p * value V h q * value V h s) * w V h * ∏ i, d V h i := by
  have hr : radial V h 4 = 2 * w V h := by change ((2 : ℕ) : Γ(threefold ψ,V)) * _ = _; norm_num
  simpa only [matrix, row_eq, CycleQ2HodgeFermatYukawaDeterminant.matrix] using
    CycleQ2HodgeFermatYukawaDeterminant.residue_evaluation (radial V h) (d V h)
      (value V h p) (value V h q) (value V h s) (w V h) hr

end CycleQ2HodgeFermatYukawaRows
end
#print axioms CycleQ2HodgeFermatYukawaRows.native_determinant
