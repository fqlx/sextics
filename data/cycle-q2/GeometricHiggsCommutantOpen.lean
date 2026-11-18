import Proposal.GeometricFormalInputs01Part02
import Proposal.SolutionSupport02Part02
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.RingTheory.Localization.Away.Basic

/-!
# A principal scalar-commutant locus through the Fermat Higgs tuple

Removing the scalar part of an endomorphism sets its (0,0)-entry to zero.
The remaining entries are coordinates on which the simultaneous equations
`P.transpose * H m = H m * P` act linearly. The literal Fermat theorem
makes this linear system injective. Independent rows of its matrix define
one maximal minor which is nonzero at Fermat. The same rows work over every
commutative ring where this minor becomes a unit.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2GeometricHiggsCommutantOpen

open Matrix
open scoped BigOperators

abbrev Index := Fin 33
abbrev Coordinate := {ij : Index × Index // ij ≠ (0,0)}
abbrev Equation := Fin 35 × Index × Index
abbrev Tuple (R : Type*) := Fin 35 → Matrix Index Index R

variable {R S : Type*} [CommRing R] [CommRing S]

/-- Fill in the missing (0,0) entry with zero. -/
def expand (x : Coordinate → R) : Matrix Index Index R :=
  fun i j => if h : (i,j) ≠ (0,0) then x ⟨(i,j),h⟩ else 0

private theorem expand_add (x y : Coordinate → R) :
    expand (x+y) = expand x + expand y := by
  ext i j
  by_cases h : (i,j) ≠ (0,0) <;> simp [expand, h]

private theorem expand_smul (c : R) (x : Coordinate → R) :
    expand (c • x) = c • expand x := by
  ext i j
  by_cases h : (i,j) ≠ (0,0) <;> simp [expand, h]

/-- The restricted simultaneous self-adjointness equations for all 35 matrices. -/
def equationMap (H : Tuple R) : (Coordinate → R) →ₗ[R] Equation → R where
  toFun x q := (((expand x).transpose * H q.1) - H q.1 * expand x) q.2.1 q.2.2
  map_add' x y := by
    funext q
    simp only [expand_add, transpose_add, add_mul, mul_add, Matrix.sub_apply, Matrix.add_apply, Pi.add_apply]
    abel
  map_smul' c x := by
    funext q
    simp only [expand_smul, transpose_smul, Matrix.smul_mul, Matrix.mul_smul, ← smul_sub,
      Matrix.smul_apply, Pi.smul_apply, RingHom.id_apply]

def coefficients (H : Tuple R) : Matrix Equation Coordinate R :=
  LinearMap.toMatrix' (equationMap H)

theorem coefficients_mulVec (H : Tuple R) (x : Coordinate → R) :
    (coefficients H).mulVec x = equationMap H x :=
  LinearMap.toMatrix'_mulVec _ _

theorem equationMap_eq_zero_iff (H : Tuple R) (x : Coordinate → R) :
    equationMap H x = 0 ↔ ∀ m, (expand x).transpose * H m = H m * expand x := by
  constructor
  · intro h m
    ext i j
    exact sub_eq_zero.mp (congrFun h (m,i,j))
  · intro h
    funext q
    change (((expand x).transpose * H q.1) - H q.1 * expand x) q.2.1 q.2.2 = 0
    rw [h, sub_self, Matrix.zero_apply]

abbrev fermat : Tuple ℂ := CycleQ2FermatHiggs.higgsMatrix ℂ

theorem fermat_injective : Function.Injective (coefficients fermat).mulVec := by
  change Function.Injective (coefficients fermat).mulVecLin
  apply (LinearMap.ker_eq_bot).mp
  rw [LinearMap.ker_eq_bot']
  intro x hx
  change (coefficients fermat).mulVec x = 0 at hx
  rw [coefficients_mulVec, equationMap_eq_zero_iff] at hx
  obtain ⟨c, hc⟩ := CycleQ2FermatHiggs.scalar_of_higgs_equations (expand x) hx
  have hc0 : (0 : ℂ) = c := by simpa [expand] using hc 0 0
  funext p
  simpa [expand, p.property, ← hc0] using hc p.val.1 p.val.2

private theorem exists_rows :
    ∃ e : Coordinate ↪ Equation, ((coefficients fermat).submatrix e id).det ≠ 0 := by
  classical
  let M := coefficients fermat
  have hrank : M.rank = Fintype.card Coordinate := by
    rw [Matrix.rank, LinearMap.finrank_range_of_inj fermat_injective, Module.finrank_pi]
  obtain ⟨κ, a, ha, hspan, hli⟩ := exists_linearIndependent' ℂ M.row
  let : Fintype κ := Fintype.ofInjective a ha
  have hcard : Fintype.card κ = Fintype.card Coordinate := by
    rw [← finrank_span_eq_card hli, hspan, ← Matrix.rank_eq_finrank_span_row M, hrank]
  let e : Coordinate ≃ κ := Fintype.equivOfCardEq hcard.symm
  refine ⟨⟨a ∘ e, ha.comp e.injective⟩, ?_⟩
  apply IsUnit.ne_zero
  apply (Matrix.isUnit_iff_isUnit_det _).mp
  apply Matrix.linearIndependent_rows_iff_isUnit.mp
  exact hli.comp e e.injective

/-- Select independent equations once, using only the literal Fermat matrices. -/
def rows : Coordinate ↪ Equation := Classical.choose exists_rows

def minor (H : Tuple R) : R := ((coefficients H).submatrix rows id).det

theorem fermat_minor_ne_zero : minor fermat ≠ 0 := Classical.choose_spec exists_rows

theorem coordinate_card : Fintype.card Coordinate = 1088 := by
  change Fintype.card {p : Index × Index // ¬p = (0,0)} = _
  simp [Fintype.card_subtype_compl, Index]

theorem minor_smul (c : R) (H : Tuple R) : minor (c • H) = c ^ 1088 * minor H := by
  have hs : coefficients (c • H) = c • coefficients H := by
    ext q p
    simp only [coefficients, LinearMap.toMatrix'_apply, equationMap, LinearMap.coe_mk,
      AddHom.coe_mk, Pi.smul_apply, Matrix.mul_smul, Matrix.smul_mul, ← smul_sub,
      Matrix.smul_apply]
  calc
    _ = (c • (coefficients H).submatrix rows id).det := by rw [minor, hs]; rfl
    _ = _ := by rw [Matrix.det_smul, coordinate_card]; rfl

def mapTuple (φ : R →+* S) (H : Tuple R) : Tuple S := fun m => (H m).map φ

theorem map_coefficients (φ : R →+* S) (H : Tuple R) :
    (coefficients H).map φ = coefficients (mapTuple φ H) := by
  ext q p
  simp only [coefficients, Matrix.map_apply, LinearMap.toMatrix'_apply, equationMap,
    LinearMap.coe_mk, AddHom.coe_mk, Matrix.sub_apply, Matrix.mul_apply, Matrix.transpose_apply,
    map_sub, map_sum, map_mul, mapTuple, expand, Pi.single_apply]
  simp [apply_dite φ, apply_ite φ]

theorem map_minor (φ : R →+* S) (H : Tuple R) :
    φ (minor H) = minor (mapTuple φ H) := by
  unfold minor
  rw [RingHom.map_det, ← map_coefficients]
  rfl

theorem minor_ne_zero_of_fermat_specialization (H : Tuple R) (φ : R →+* ℂ)
    (he : mapTuple φ H = fermat) : minor H ≠ 0 := by
  intro hz
  apply fermat_minor_ne_zero
  rw [← he, ← map_minor, hz, map_zero]

theorem minor_ne_zero_of_scaled_fermat_specialization (H : Tuple R) (φ : R →+* ℂ)
    {c : ℂ} (hc : c ≠ 0) (he : mapTuple φ H = c • fermat) : minor H ≠ 0 := by
  intro hz
  have hw := map_minor φ H
  rw [he, minor_smul, hz, map_zero] at hw
  exact (mul_ne_zero (pow_ne_zero _ hc) fermat_minor_ne_zero) hw.symm

/-- The same fixed rows detect all endomorphisms after any base change in
which their determinant is a unit. -/
theorem scalar_of_minor_isUnit (H : Tuple R) (h : IsUnit (minor H))
    (P : Matrix Index Index R) (hP : ∀ m, P.transpose * H m = H m * P) :
    ∃ c : R, P = c • (1 : Matrix Index Index R) := by
  classical
  let c := P 0 0
  let Q := P - c • (1 : Matrix Index Index R)
  let x : Coordinate → R := fun p => Q p.val.1 p.val.2
  have hx : expand x = Q := by
    ext i j
    by_cases hij : (i,j) ≠ (0,0)
    · simp [expand, x, hij]
    · have he := not_not.mp hij
      obtain ⟨rfl, rfl⟩ := Prod.mk.inj he
      simp [expand, Q, c]
  have hQ : ∀ m, Q.transpose * H m = H m * Q := by
    intro m
    simp only [Q, transpose_sub, transpose_smul, transpose_one, sub_mul, mul_sub,
      Matrix.smul_mul, Matrix.mul_smul, one_mul, mul_one, hP]
  have hz : (coefficients H).mulVec x = 0 := by
    rw [coefficients_mulVec, equationMap_eq_zero_iff, hx]
    exact hQ
  let M := (coefficients H).submatrix rows id
  have hx0 : x = 0 := by
    apply Matrix.mulVec_injective_of_det_mem_nonZeroDivisors (M := M) h.mem_nonZeroDivisors
    rw [Matrix.mulVec_zero]
    exact funext (fun p => congrFun hz (rows p))
  refine ⟨c, sub_eq_zero.mp ?_⟩
  change Q = 0
  rw [← hx, hx0]
  ext i j
  by_cases h : (i,j) ≠ (0,0) <;> simp [expand,h]

/-- Over a domain every compatible projector on this principal open is trivial. -/
theorem projector_trivial_of_minor_isUnit [IsDomain R] (H : Tuple R) (h : IsUnit (minor H))
    (P : Matrix Index Index R) (hP : ∀ m, P.transpose * H m = H m * P)
    (hidem : P * P = P) : P = 0 ∨ P = 1 := by
  obtain ⟨c, rfl⟩ := scalar_of_minor_isUnit H h P hP
  have hc := congrArg (fun M : Matrix Index Index R => M 0 0) hidem
  have he : c * c = c := by
    simpa only [Matrix.smul_mul, Matrix.mul_smul, one_mul, Matrix.smul_apply,
      smul_eq_mul, Matrix.one_apply_eq, mul_one] using hc
  rcases (mul_eq_zero.mp (show c * (c - 1) = 0 by rw [mul_sub, he, mul_one, sub_self])) with hz | ho
  · simp [hz]
  · simp [sub_eq_zero.mp ho]

theorem scalar_on_principal_open (H : Tuple R)
    (P : Matrix Index Index (Localization.Away (minor H)))
    (hP : ∀ m, P.transpose * mapTuple (algebraMap R _) H m =
      mapTuple (algebraMap R _) H m * P) :
    ∃ c : Localization.Away (minor H), P = c • (1 : Matrix Index Index (Localization.Away (minor H))) := by
  apply scalar_of_minor_isUnit _ _ P hP
  rw [← map_minor]
  exact IsLocalization.Away.algebraMap_isUnit (minor H)

/-- The actual Fermat point of the polynomial ring of the invariant sextic family. -/
def fermatPoint : PrimeSpectrum CycleQ2GenericSexticGradient.CoeffRing :=
  ⟨RingHom.ker CycleQ2GenericSexticGradient.seedEvaluation,
    RingHom.ker_isPrime CycleQ2GenericSexticGradient.seedEvaluation⟩

theorem fermatPoint_mem (H : Tuple CycleQ2GenericSexticGradient.CoeffRing)
    {c : ℂ} (hc : c ≠ 0) (he : mapTuple CycleQ2GenericSexticGradient.seedEvaluation H =
      c • fermat) : fermatPoint ∈ PrimeSpectrum.basicOpen (minor H) := by
  apply (PrimeSpectrum.mem_basicOpen _ _).mpr
  change CycleQ2GenericSexticGradient.seedEvaluation (minor H) ≠ 0
  rw [map_minor, he, minor_smul]
  exact mul_ne_zero (pow_ne_zero _ hc) fermat_minor_ne_zero

end CycleQ2GeometricHiggsCommutantOpen
end

#print axioms CycleQ2GeometricHiggsCommutantOpen.fermat_minor_ne_zero
#print axioms CycleQ2GeometricHiggsCommutantOpen.fermatPoint_mem
#print axioms CycleQ2GeometricHiggsCommutantOpen.scalar_on_principal_open
