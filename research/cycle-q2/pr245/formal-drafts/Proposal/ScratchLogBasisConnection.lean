import Mathlib.LinearAlgebra.ExteriorPower.Basis
import Mathlib.RingTheory.Derivation.Basic

/-! Coefficient derivatives in constant exterior frames. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogBasisConnection

variable {k R : Type*} [CommRing k] [CommRing R] [Algebra k R]
variable {M N : Type*} [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
variable {I J : Type*} [Fintype I] [Fintype J]

/-- Differentiate the coefficients in the chosen frame. -/
def coeffD (b : Module.Basis I R M) (D : Derivation k R R) : M →+ M where
  toFun x := b.equivFun.symm (fun i => D (b.equivFun x i))
  map_zero' := by simp
  map_add' x y := by
    apply b.equivFun.injective
    simp only [map_add, LinearEquiv.apply_symm_apply, Pi.add_apply] <;> rfl

theorem coeffD_coord (b : Module.Basis I R M) (D : Derivation k R R) (x : M) (i : I) :
    b.repr (coeffD b D x) i = D (b.repr x i) := by
  change b.equivFun (b.equivFun.symm _) i = _
  rw [LinearEquiv.apply_symm_apply] <;> rfl

theorem coeffD_smul (b : Module.Basis I R M) (D : Derivation k R R) (r : R) (x : M) :
    coeffD b D (r • x) = D r • x + r • coeffD b D x := by
  apply b.equivFun.injective
  funext i
  simp only [Module.Basis.equivFun_apply, coeffD_coord, map_smul, map_add,
    Finsupp.smul_apply, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Derivation.leibniz]
  ac_rfl

theorem coeffD_self (b : Module.Basis I R M) (D : Derivation k R R) (i : I) :
    coeffD b D (b i) = 0 := by
  classical
  apply b.equivFun.injective
  funext j
  simp only [Module.Basis.equivFun_apply, coeffD_coord, Module.Basis.repr_self_apply, map_zero,
    Pi.zero_apply]
  split <;> simp

/-- A matrix with coefficients killed by D commutes with the coefficient derivatives. -/
theorem coeffD_natural (b : Module.Basis I R M) (c : Module.Basis J R N)
    (D : Derivation k R R) (f : M →ₗ[R] N)
    (h : ∀ i, coeffD c D (f (b i)) = 0) (x : M) :
    coeffD c D (f x) = f (coeffD b D x) := by
  conv => lhs; rw [← b.sum_repr x]
  conv => rhs; rw [← b.sum_repr x]
  simp only [map_sum, map_smul, coeffD_smul, h, coeffD_self, smul_zero, add_zero]

/-- Every coordinate of a wedge of frame vectors is an integer. -/
theorem integral_exterior_coordinate [LinearOrder I] (b : Module.Basis I R M) (n : ℕ)
    (v : Fin n → I) (s : Set.powersetCard I n) :
    ∃ z : ℤ, (b.exteriorPower n).repr (exteriorPower.ιMulti R n (b ∘ v)) s = (z : R) := by
  classical
  let m : Matrix (Fin n) (Fin n) ℤ := Matrix.of fun i j =>
    if v i = Set.powersetCard.ofFinEmbEquiv.symm s j then 1 else 0
  refine ⟨m.det, ?_⟩
  rw [exteriorPower.basis_repr_apply, exteriorPower.ιMultiDual_apply_ιMulti]
  change _ = (Int.castRingHom R) m.det
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [m, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Function.comp_apply,
    Module.Basis.coord_apply, Module.Basis.repr_self_apply]
  split <;> simp

theorem coeffD_wedge_basis [LinearOrder I] (b : Module.Basis I R M) (n : ℕ)
    (D : Derivation k R R) (v : Fin n → I) :
    coeffD (b.exteriorPower n) D (exteriorPower.ιMulti R n (b ∘ v)) = 0 := by
  apply (b.exteriorPower n).equivFun.injective
  funext s
  obtain ⟨z,hz⟩ := integral_exterior_coordinate b n v s
  simp only [Module.Basis.equivFun_apply, coeffD_coord, hz, Derivation.map_intCast,
    map_zero, Pi.zero_apply]

end CycleQ2LogBasisConnection
end
#print axioms CycleQ2LogBasisConnection.coeffD_natural
#print axioms CycleQ2LogBasisConnection.coeffD_wedge_basis
