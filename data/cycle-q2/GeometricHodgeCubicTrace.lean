import Proposal.GeometricHodgeThreefoldCubic
import Mathlib.LinearAlgebra.Determinant
import Mathlib.LinearAlgebra.Dual.Basis
import Mathlib.Tactic

/-!
# The square-coefficient pairing on the full sextic threefold charts

On each weight-one chart the literal monic cubic makes the ring free of
rank three over the three-variable polynomial algebra. Multiplication
followed by the square coefficient pairs this algebra perfectly with itself
over that base ring, including on the ramification locus.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2HodgeCubicTrace
variable {B S : Type*} [CommRing B] [CommRing S] [Algebra B S]
variable (b : Module.Basis (Fin 3) B S) (z : S) (hb : ∀ j, b j = z ^ j.val)

/-- Multiply in the cubic algebra and take the coefficient of the square of its generator. -/
def pairing : S →ₗ[B] Module.Dual B S where
  toFun x := (b.coord 2).comp (Algebra.lmul B S x)
  map_add' x y := by ext v; change (b.coord 2) ((x+y)*v) = _; rw [add_mul,map_add]; rfl
  map_smul' a x := by ext v; change (b.coord 2) ((a • x) * v) = _; rw [smul_mul_assoc,map_smul]; rfl

include hb in
private theorem entry (i j k : Fin 3) (h : i.val + j.val = k.val) :
    LinearMap.toMatrix b b.dualBasis (pairing b) i j = if k=2 then 1 else 0 := by
  rw [LinearMap.toMatrix_apply, Module.Basis.dualBasis_repr]
  change b.repr (b j * b i) 2 = _
  have hv : b j * b i = b k := by
    simp only [hb, ← pow_add, Nat.add_comm j.val i.val, h]
  rw [hv, Module.Basis.repr_self_apply]

include hb in
theorem determinant : (LinearMap.toMatrix b b.dualBasis (pairing b)).det = -1 := by
  rw [Matrix.det_fin_three, entry b z hb 0 0 0 (by decide), entry b z hb 0 1 1 (by decide),
      entry b z hb 0 2 2 (by decide), entry b z hb 1 0 1 (by decide),
      entry b z hb 1 1 2 (by decide), entry b z hb 2 0 2 (by decide)]
  simp [show (0 : Fin 3) ≠ 2 from by decide, show (1 : Fin 3) ≠ 2 from by decide]

def perfect : S ≃ₗ[B] Module.Dual B S :=
  LinearEquiv.ofIsUnitDet (v := b) (v' := b.dualBasis) (f := pairing b) <| by
    rw [determinant b z hb]
    exact isUnit_one.neg

theorem perfect_apply (x y : S) : perfect b z hb x y = b.repr (x*y) 2 := rfl

section Chart

open CycleQ2GeometricHodgeThreefoldCubic
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (vertexCoefficient)

variable {R : Type} [CommRing R] [Nontrivial R] (φ : CoeffRing →+* R)
  (i : Fin 4) (h : IsUnit (φ vertexCoefficient))

/-- Perfect relative residue pairing on the actual dehomogenization of the universal sextic. -/
def chartEquiv : AdjoinRoot (cubic φ i h) ≃ₗ[Base R] Module.Dual (Base R) (AdjoinRoot (cubic φ i h)) :=
  perfect (basis φ i h) (AdjoinRoot.root _) (basis_apply φ i h)

theorem chartEquiv_apply (x y : AdjoinRoot (cubic φ i h)) :
    chartEquiv φ i h x y = (basis φ i h).repr (x*y) 2 := rfl

end Chart
end CycleQ2HodgeCubicTrace

#print axioms CycleQ2HodgeCubicTrace.chartEquiv
#print axioms CycleQ2HodgeCubicTrace.chartEquiv_apply
