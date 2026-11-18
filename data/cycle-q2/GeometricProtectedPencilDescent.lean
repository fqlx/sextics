import Proposal.GeometricProtectedPencilSourceForm
import Mathlib.FieldTheory.IntermediateField.Basic

/-!
# The protected residue four-form on the fixed field of the sign involution

The invariant coordinates are the square of X₂, Y₀, Y₁, and the pencil
parameter. Their Jacobian in the protected function field has determinant
two, which fixes the normalization of the descended top form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2ProtectedPencilDescent

open HodgeComputer CycleQ2AffineClearing CycleQ2AffineHypersurface CycleQ2AffineDifferentials
  CycleQ2AffineExterior CycleQ2AffineExactness CycleQ2AffineResidueClosure
  CycleQ2GeometricAffineOverlap CycleQ2ExteriorSectionNaturality CycleQ2ProtectedPencilAction
  CycleQ2ProtectedPencilSourceForm HoldoutConstruction SplitHigherResidue
open CycleQ2AffineWeightedTransfer (u z E parameter E_u E_apply E_parameter_zero
  E_parameter_one E_parameter_two E_parameter_three u_ne_zero)

local instance : CharZero K := charZero_of_injective_algebraMap (algebraMap ℂ K).injective

def betaFixed : IntermediateField ℂ K where
  toSubalgebra := AlgHom.equalizer beta.toAlgHom (AlgHom.id ℂ K)
  inv_mem' x (hx : beta x = x) := by change beta x⁻¹ = x⁻¹; rw [map_inv₀, hx]

theorem mem_betaFixed (x : K) : x ∈ betaFixed ↔ beta x = x := Iff.rfl

def fixedCoordinates : Fin 4 → betaFixed :=
  ![⟨u ^ 2, by rw [mem_betaFixed, map_pow]; simp [u, beta_coordinate, betaScale]⟩,
    ⟨z 2, by rw [mem_betaFixed, beta_coordinate]; change algebraMap ℂ K 1 * _ = _; simp⟩,
    ⟨z 3, by rw [mem_betaFixed, beta_coordinate]; change algebraMap ℂ K 1 * _ = _; simp⟩,
    ⟨parameter, beta_parameter⟩]

def fixedCoefficient : betaFixed :=
  ⟨affineNormalSource affineA / normalDensity, by
    simpa only [mem_betaFixed, AlgEquiv.coe_toAlgHom, map_one, one_mul] using
      coefficient_character (diagonal betaScale) betaScale (diagonal_X _) (by rfl)
        beta.toAlgHom beta_affineMap 1 beta_F (by simpa only [map_one, one_mul] using beta_A)⟩

attribute [local irreducible] betaFixed

set_option synthInstance.maxHeartbeats 100000
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

def halfCoordinateVolume {F : Type} [Field F] [Algebra ℂ F] (x : Fin 4 → F) :
    ⋀[F]^4 (KaehlerDifferential ℂ F) :=
  (2 : F)⁻¹ • exteriorPower.ιMulti F 4 (fun i => KaehlerDifferential.D ℂ F (x i))

def coefficientVolume {F : Type} [Field F] [Algebra ℂ F] (c : F)
    (ω : ⋀[F]^4 (KaehlerDifferential ℂ F)) : ⋀[F]^4 (KaehlerDifferential ℂ F) := c • ω

theorem halfCoordinateVolume_map {F B : Type} [Field F] [Field B] [Algebra ℂ F] [Algebra ℂ B]
    (f : F →ₐ[ℂ] B) (x : Fin 4 → F) :
    exteriorDifferentialMap f 4 (halfCoordinateVolume x) = halfCoordinateVolume (fun i => f (x i)) := by
  rw [halfCoordinateVolume, map_smulₛₗ, exteriorDifferentialMap_wedge]
  simp only [map_inv₀, map_ofNat, differentialMap_D, halfCoordinateVolume]

theorem coefficientVolume_map {F B : Type} [Field F] [Field B] [Algebra ℂ F] [Algebra ℂ B]
    (f : F →ₐ[ℂ] B) (c : F) (ω : ⋀[F]^4 (KaehlerDifferential ℂ F)) :
    exteriorDifferentialMap f 4 (coefficientVolume c ω) =
      coefficientVolume (f c) (exteriorDifferentialMap f 4 ω) :=
  (exteriorDifferentialMap f 4).map_smulₛₗ c ω

def descendedVolume : ⋀[betaFixed]^4 (KaehlerDifferential ℂ betaFixed) :=
  halfCoordinateVolume fixedCoordinates

def descendedSource : ⋀[betaFixed]^4 (KaehlerDifferential ℂ betaFixed) :=
  coefficientVolume fixedCoefficient descendedVolume

private def ambientCoordinates : Fin 4 → K := ![u^2, z 2, z 3, parameter]

private theorem coordinates_val (i : Fin 4) : betaFixed.val (fixedCoordinates i) = ambientCoordinates i := by
  fin_cases i <;> rfl

private def jacobian : Matrix (Fin 4) (Fin 4) K :=
  !![2*u, 0, 0, -parameter/u; 0, 1, 0, 0; 0, 0, 1, 0; 0, 0, 0, 1/u]

set_option backward.isDefEq.respectTransparency false in
set_option backward.isDefEq.respectTransparency.types false in
private theorem coordinate_matrix :
    coordinateBasis.toMatrix (fun i => d (ambientCoordinates i)) = jacobian := by
  have hY (i j : Fin 4) : E i (z j.succ) = if j = i then 1 else 0 :=
    affineTangent_coordinate i j
  have hY₀ (i : Fin 4) : E i (z 2) = if 1 = i then 1 else 0 := hY i 1
  have hY₁ (i : Fin 4) : E i (z 3) = if 2 = i then 1 else 0 := hY i 2
  ext i j
  rw [Module.Basis.toMatrix_apply, coordinateBasis_repr_d, ← E_apply]
  fin_cases i <;> fin_cases j <;>
    norm_num [ambientCoordinates, jacobian, hY₀, hY₁, Derivation.leibniz_pow, smul_eq_mul,
      nsmul_eq_mul, Matrix.cons_val_two, Matrix.cons_val_three, Matrix.head_cons,
      Matrix.tail_cons, -E_apply]
  case «2».«3» => exact E_parameter_two
  case «3».«3» => exact E_parameter_three.trans (one_div u)
  all_goals decide

private theorem jacobian_det : jacobian.det = 2 := by
  rw [Matrix.det_succ_column_zero]
  simp [Fin.sum_univ_succ, jacobian, Matrix.det_fin_three, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.head_cons, Matrix.tail_cons]
  field_simp [u_ne_zero]

theorem descendedVolume_pullback : exteriorDifferentialMap betaFixed.val 4 descendedVolume = volume := by
  rw [descendedVolume, halfCoordinateVolume_map]
  simp_rw [coordinates_val]
  change (2 : K)⁻¹ • exteriorPower.ιMulti K 4 (fun i => d (ambientCoordinates i)) = volume
  rw [CycleQ2ResidueWedgeLinear.topWedge_eq_det_smul coordinateBasis, coordinate_matrix,
    jacobian_det, smul_smul]
  norm_num [volume, show (⇑coordinateBasis) = coordinateDifferential from funext coordinateBasis_apply]

theorem descendedSource_pullback :
    exteriorDifferentialMap betaFixed.val 4 descendedSource = residueSourceForm affineA := by
  rw [descendedSource, coefficientVolume_map, descendedVolume_pullback]
  rfl

end CycleQ2ProtectedPencilDescent
end

#print axioms CycleQ2ProtectedPencilDescent.descendedVolume_pullback
#print axioms CycleQ2ProtectedPencilDescent.descendedSource_pullback
