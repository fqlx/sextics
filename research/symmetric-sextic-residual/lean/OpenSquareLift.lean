import Proposal.SymmetricContactField

noncomputable section
namespace OpenSquareLift
open MvPolynomial HoldoutConstruction ReflectionCoupledFano
open scoped BigOperators
set_option maxHeartbeats 1000000
set_option backward.isDefEq.respectTransparency false
set_option maxRecDepth 10000

variable {R : Type*} [CommRing R]
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

abbrev Index (ι : Type*) := ι ⊕ Unit

def equations (F : ι → MvPolynomial ι R) (q : MvPolynomial ι R) :
    Index ι → MvPolynomial (Index ι) R
  | Sum.inl i => rename Sum.inl (F i)
  | Sum.inr _ => rename Sum.inl q * X (Sum.inr ()) - 1

def seed {T : Type*} [Field T] [Algebra R T]
    (y : ι → T) (q : MvPolynomial ι R) : Index ι → T :=
  Sum.elim y (fun _ => (aeval y q)⁻¹)

theorem root_original {T : Type*} [CommRing T] [Algebra R T]
    (F : ι → MvPolynomial ι R) (q : MvPolynomial ι R) (z : Index ι → T)
    (hz : ∀ i, aeval z (equations F q i) = 0) (i : ι) :
    aeval (fun j => z (Sum.inl j)) (F i) = 0 := by
  simpa [equations,aeval_rename,Function.comp_def] using hz (Sum.inl i)

theorem root_unit {T : Type*} [CommRing T] [Algebra R T]
    (F : ι → MvPolynomial ι R) (q : MvPolynomial ι R) (z : Index ι → T)
    (hz : ∀ i, aeval z (equations F q i) = 0) :
    IsUnit (aeval (fun j => z (Sum.inl j)) q) := by
  have h := hz (Sum.inr ())
  simp only [equations,map_sub,map_mul,map_one,aeval_X,
    aeval_rename,Function.comp_def,sub_eq_zero] at h
  exact IsUnit.of_mul_eq_one (z (Sum.inr ())) h

/-- The new inverse coordinate gives a block triangular Jacobian at EVERY
point, not just the seed. -/
theorem jacobian_det {T : Type*} [CommRing T] [Algebra R T]
    (F : ι → MvPolynomial ι R) (q : MvPolynomial ι R) (z : Index ι → T) :
    Matrix.det (fun i j : Index ι => aeval z (pderiv i (equations F q j))) =
      Matrix.det (fun i j : ι => aeval (fun k => z (Sum.inl k)) (pderiv i (F j))) *
        aeval (fun k => z (Sum.inl k)) q := by
  let M : Matrix ι ι T := fun i j => aeval (fun k => z (Sum.inl k)) (pderiv i (F j))
  let B : Matrix ι Unit T := fun i j => aeval z (pderiv (Sum.inl i) (equations F q (Sum.inr j)))
  let Q : Matrix Unit Unit T := fun _ _ => aeval (fun k => z (Sum.inl k)) q
  have hm : (fun i j : Index ι => aeval z (pderiv i (equations F q j))) =
      Matrix.fromBlocks M B 0 Q := by
    ext i j
    cases i with
    | inl i =>
      cases j with
      | inl j => simp [Matrix.fromBlocks,equations,pderiv_rename Sum.inl_injective,aeval_rename,M,Function.comp_def]
      | inr j => rfl
    | inr i =>
      cases j with
      | inl j => simp [equations,SymmetricContactField.pderiv_inr_rename_inl]
      | inr j =>
        cases i; cases j
        simp [Matrix.fromBlocks,equations,pderiv_mul,SymmetricContactField.pderiv_inr_rename_inl,
          pderiv_X,Pi.single_apply,aeval_rename,Q,Function.comp_def]
  rw [hm,Matrix.det_fromBlocks_zero₂₁]
  have hQ : Matrix.det Q = aeval (fun k => z (Sum.inl k)) q := by
    simpa only [Q] using Matrix.det_unique Q
  rw [hQ]

theorem seed_equations {T : Type*} [Field T] [Algebra R T]
    (F : ι → MvPolynomial ι R) (q : MvPolynomial ι R) (y : ι → T)
    (hy : ∀ i, aeval y (F i) = 0) (hq : IsUnit (aeval y q)) :
    ∀ i, aeval (seed y q) (equations F q i) = 0 := by
  intro i
  cases i with
  | inl i => simpa [equations,seed,aeval_rename,Function.comp_def] using hy i
  | inr i => simp [equations,seed,aeval_rename,Function.comp_def,hq.ne_zero]

theorem seed_jacobian {T : Type*} [Field T] [Algebra R T]
    (F : ι → MvPolynomial ι R) (q : MvPolynomial ι R) (y : ι → T)
    (hj : IsUnit (Matrix.det (fun i j => aeval y (pderiv i (F j)))))
    (hq : IsUnit (aeval y q)) :
    IsUnit (Matrix.det (fun i j => aeval (seed y q) (pderiv i (equations F q j)))) := by
  rw [jacobian_det]
  simpa only [seed,Sum.elim_inl] using hj.mul hq

/-- A polynomial open verified at a nonsingular special point can be
retained in a NEW finite separable generic field factor.  Both the old
Jacobian unit and the extra polynomial unit are conclusions. -/
theorem exists_field_with_unit
    {K T : Type*} [Field K] [Field T] [Algebra R K] [Algebra R T]
    (F : ι → MvPolynomial ι R) (q : MvPolynomial ι R) (y : ι → T)
    (hy : ∀ i, aeval y (F i) = 0)
    (hj : IsUnit (Matrix.det (fun i j => aeval y (pderiv i (F j)))))
    (hq : IsUnit (aeval y q)) (hinj : Function.Injective (algebraMap R K)) :
    ∃ I : Ideal (SquareGenericAlgebra K (equations F q)), I.IsMaximal ∧
      Module.Finite K ((SquareGenericAlgebra K (equations F q)) ⧸ I) ∧
      Algebra.IsSeparable K ((SquareGenericAlgebra K (equations F q)) ⧸ I) ∧
      (∀ i, aeval (squareGenericCoordinates (equations F q) I) (equations F q i) = 0) ∧
      IsUnit (Matrix.det (fun i j => aeval
        (squareGenericCoordinates (equations F q) I) (pderiv i (equations F q j)))) := by
  exact square_system_generic_lift (R := R) (K := K) (T := T) (equations F q) (seed y q)
    (seed_equations F q y hy hq) (seed_jacobian F q y hj hq) hinj

#print axioms jacobian_det
#print axioms exists_field_with_unit
end OpenSquareLift
