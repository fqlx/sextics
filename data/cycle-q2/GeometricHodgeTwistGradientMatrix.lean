import Proposal.GeometricHodgeEuler
import Proposal.GeometricHodgeThreefoldProper

/-!
# A degree-24 conversion matrix for the four projective gradient denominators

The existing Macaulay minor controls all five Euler generators in degree
thirty. Weighted Euler eliminates the fifth generator while recording the
multiple of the original hypersurface equation. Choosing the four rows
over the actual localized coefficient base gives one matrix that
specializes coefficientwise to every fiber.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeTwistGradientMatrix
open MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing gradientOpen generators degree degree_le
  generators_homogeneous coordinatePower coordinatePower_homogeneous coordinate_power_mem)
open CycleQ2GeometricHodgeThreefold (equation equation_homogeneous quotient coord equation_zero)
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2IncidenceEquations (HG)
open CycleQ2IncidenceNormalForm (fullGrading)
open CycleQ2HomogeneousIdealArithmetic (homogeneous_membership homogeneous_map)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)
abbrev Poly (R : Type) [CommRing R] := MvPolynomial (Fin 5) R

def g (j : Fin 5) : Poly R := X j * pderiv j (equation φ)

private theorem map_generator (j : Fin 5) : MvPolynomial.map φ (generators j) = g φ j := by
  rw [generators, map_mul, map_X, ← pderiv_map]
  rfl

private theorem euler : (∑ j : Fin 4, g φ j.castSucc) + 2 * g φ (Fin.last 4) = 6 * equation φ := by
  have h := (equation_homogeneous φ).sum_weight_X_mul_pderiv
  rw [Fin.sum_univ_castSucc] at h
  simpa only [CycleQ2SeedFermatProj.geometricWeight_castSucc, one_smul, nsmul_eq_mul,
    show geometricWeight (Fin.last 4) = 2 from rfl, Nat.cast_ofNat, g] using h

structure System where
  matrix : Matrix (Fin 4) (Fin 4) (Poly R)
  remainder : Fin 4 → Poly R
  entryDegree (i j : Fin 4) : HG (matrix i j) (24,0)
  remainderDegree (i : Fin 4) : HG (remainder i) (24,0)
  relation (i : Fin 4) : X i.castSucc ^ 30 = (∑ j : Fin 4, matrix i j * g φ j.castSucc) +
    remainder i * equation φ

private theorem exists_row (hg : IsUnit (φ gradientOpen)) (i : Fin 4) :
    ∃ (A : Fin 4 → Poly R) (b : Poly R), (∀ j, HG (A j) (24,0)) ∧ HG b (24,0) ∧
      X i.castSucc ^ 30 = (∑ j : Fin 4, A j * g φ j.castSucc) + b * equation φ := by
  have h30 : coordinatePower i.castSucc = 30 := by fin_cases i <;> rfl
  obtain ⟨u,hu,he⟩ := homogeneous_membership (fun j => MvPolynomial.map φ (generators j)) degree
    (fun j => homogeneous_map φ (generators_homogeneous j)) 30 degree_le _
    (coordinatePower_homogeneous i.castSucc) (coordinate_power_mem φ hg i.castSucc)
  simp only [map_generator, h30, Fin.sum_univ_castSucc] at he
  let k : R := φ (C ((2 : ℂ)⁻¹))
  let v : Poly R := C k * u (Fin.last 4)
  have hv : HG v (24,0) := by
    simpa only [v, smul_eq_C_mul] using (weightedHomogeneousSubmodule R fullGrading (24,0)).smul_mem
      k (show HG (u (Fin.last 4)) (24,0) from hu _)
  have h2 : (2 : Poly R) * C k = 1 := by
    let f : ℂ →+* Poly R := C.comp (φ.comp C)
    simpa only [map_mul, map_ofNat, map_one] using
      congrArg f (mul_inv_cancel₀ (show (2 : ℂ) ≠ 0 by norm_num))
  have hw : (2 : Poly R) * v = u (Fin.last 4) := by rw [show 2*v = 2*C k * u (Fin.last 4) from (mul_assoc _ _ _).symm, h2, one_mul]
  refine ⟨fun j => u j.castSucc - v, 6*v, fun j => (show HG (u j.castSucc) (24,0) from hu _).sub hv, ?_, ?_⟩
  · simpa only [nsmul_eq_mul, Nat.cast_ofNat] using (weightedHomogeneousSubmodule R fullGrading (24,0)).nsmul_mem hv 6
  · rw [he, ← hw]
    simp only [sub_mul, Finset.sum_sub_distrib, ← Finset.mul_sum]
    have heuler := euler φ
    have hcomm : (∑ j : Fin 4, g φ j.castSucc * u j.castSucc) = ∑ j : Fin 4, u j.castSucc * g φ j.castSucc :=
      Finset.sum_congr rfl (fun _ _ => mul_comm _ _)
    rw [hcomm]
    linear_combination v * heuler

def system (hg : IsUnit (φ gradientOpen)) : System φ := by
  choose A b hA hb he using exists_row φ hg
  exact ⟨A,b,hA,hb,he⟩

abbrev Base := Localization.Away gradientOpen
abbrev baseMap : CoeffRing →+* Base := algebraMap _ _

/-- The matrix is chosen once over the open in the original parameter space. -/
def universalSystem : System baseMap := system baseMap (IsLocalization.Away.algebraMap_isUnit gradientOpen)

theorem map_g {S : Type} [CommRing S] (f : R →+* S) (j : Fin 5) :
    MvPolynomial.map f (g φ j) = g (f.comp φ) j := by
  simp only [g, equation, map_mul, map_X, ← pderiv_map, map_map]

def System.baseChange {S : Type} [CommRing S] (T : System φ) (f : R →+* S) : System (f.comp φ) where
  matrix := T.matrix.map (MvPolynomial.map f)
  remainder i := MvPolynomial.map f (T.remainder i)
  entryDegree i j := homogeneous_map f (T.entryDegree i j)
  remainderDegree i := homogeneous_map f (T.remainderDegree i)
  relation i := by
    have he := congrArg (MvPolynomial.map f) (T.relation i)
    simpa only [map_pow, map_X, map_add, map_mul, map_sum, map_g, equation, map_map, Matrix.map_apply] using he

def fiberMap (hg : IsUnit (φ gradientOpen)) : Base →+* R :=
  IsLocalization.Away.lift gradientOpen hg

@[simp] theorem fiberMap_baseMap (hg : IsUnit (φ gradientOpen)) : (fiberMap φ hg).comp baseMap = φ :=
  IsLocalization.Away.lift_comp _ _

def fiberSystem (hg : IsUnit (φ gradientOpen)) : System φ where
  matrix := universalSystem.matrix.map (MvPolynomial.map (fiberMap φ hg))
  remainder i := MvPolynomial.map (fiberMap φ hg) (universalSystem.remainder i)
  entryDegree i j := homogeneous_map _ (universalSystem.entryDegree i j)
  remainderDegree i := homogeneous_map _ (universalSystem.remainderDegree i)
  relation i := by
    simpa only [fiberMap_baseMap] using (System.baseChange baseMap universalSystem (fiberMap φ hg)).relation i

theorem System.detDegree (T : System φ) : HG T.matrix.det (96,0) := by
  classical
  rw [Matrix.det_apply]
  apply (weightedHomogeneousSubmodule R fullGrading (96,0)).sum_mem
  intro σ _
  change (↑(Equiv.Perm.sign σ) : ℤ) • (∏ i, T.matrix (σ i) i) ∈ _
  apply (weightedHomogeneousSubmodule R fullGrading (96,0)).zsmul_mem
  rw [Fin.prod_univ_four]
  exact (((T.entryDegree _ _).mul (T.entryDegree _ _)).mul (T.entryDegree _ _)).mul (T.entryDegree _ _)

/-- The correction is precisely a multiple of F, hence disappears in the actual native cone. -/
theorem System.cone_relation (T : System φ) (i : Fin 4) : coord φ i.castSucc ^ 30 =
    ∑ j : Fin 4, quotient φ (T.matrix i j) * (coord φ j.castSucc * quotient φ (pderiv j.castSucc (equation φ))) := by
  have he := congrArg (quotient φ) (T.relation i)
  simpa only [map_pow, map_add, map_sum, g, map_mul, equation_zero, mul_zero, add_zero, coord] using he

end CycleQ2HodgeTwistGradientMatrix
end
#print axioms CycleQ2HodgeTwistGradientMatrix.universalSystem
#print axioms CycleQ2HodgeTwistGradientMatrix.System.baseChange
#print axioms CycleQ2HodgeTwistGradientMatrix.System.cone_relation
