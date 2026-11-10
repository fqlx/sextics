import HodgeComputer.Constructions.HoldoutCover.GenericIncidence

noncomputable section
open scoped TensorProduct
namespace CompleteIncidenceCoordinates
open HoldoutConstruction
variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
variable {ι : Type*} [Fintype ι]

def quotientMap (F : ι → MvPolynomial ι R) :
    SquareSystemRing F →ₐ[R] SquareGenericAlgebra K F :=
  (Algebra.TensorProduct.includeRight : SquareEtaleRing F →ₐ[R] SquareGenericAlgebra K F).comp
    (IsScalarTower.toAlgHom R (SquareSystemRing F) (SquareEtaleRing F))

def coordinates (F : ι → MvPolynomial ι R) (i : ι) : SquareGenericAlgebra K F :=
  quotientMap R K F (Ideal.Quotient.mk _ (MvPolynomial.X i))

theorem evaluation (F : ι → MvPolynomial ι R) (p : MvPolynomial ι R) :
    MvPolynomial.aeval (coordinates R K F) p =
      quotientMap R K F (Ideal.Quotient.mk _ p) := by
  have h : MvPolynomial.aeval (coordinates R K F) =
      (quotientMap R K F).comp (Ideal.Quotient.mkₐ R _) := by
    apply MvPolynomial.algHom_ext
    intro i
    simp [coordinates]
  exact congrArg (fun e : MvPolynomial ι R →ₐ[R] _ => e p) h

theorem solution (F : ι → MvPolynomial ι R) (i : ι) :
    MvPolynomial.aeval (coordinates R K F) (F i) = 0 := by
  rw [evaluation]
  have h : Ideal.Quotient.mk (Ideal.span (Set.range F)) (F i) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i,rfl⟩)
  rw [h,map_zero]

theorem jacobian_unit [DecidableEq ι] (F : ι → MvPolynomial ι R) :
    IsUnit (Matrix.det (fun i j => MvPolynomial.aeval (coordinates R K F)
      (MvPolynomial.pderiv i (F j)))) := by
  have hj := IsLocalization.Away.algebraMap_isUnit
    (S := SquareEtaleRing F) (squareSystemJacobian F)
  have hm := hj.map (Algebra.TensorProduct.includeRight :
    SquareEtaleRing F →ₐ[R] SquareGenericAlgebra K F).toRingHom
  change IsUnit (quotientMap R K F (squareSystemJacobian F)) at hm
  have he : quotientMap R K F (squareSystemJacobian F) =
      Matrix.det (fun i j => MvPolynomial.aeval (coordinates R K F)
        (MvPolynomial.pderiv i (F j))) := by
    have hcanon := congrArg (quotientMap R K F) (squareSystemJacobian_eq_mk_det F)
    calc
      _ = quotientMap R K F (Ideal.Quotient.mk _
          (Matrix.det (fun i j => MvPolynomial.pderiv i (F j)))) := hcanon
      _ = MvPolynomial.aeval (coordinates R K F)
          (Matrix.det (fun i j => MvPolynomial.pderiv i (F j))) :=
        (evaluation R K F _).symm
      _ = _ := AlgHom.map_det _ _
  exact he ▸ hm

theorem factor_coordinates [DecidableEq ι] (F : ι → MvPolynomial ι R)
    (I : Ideal (SquareGenericAlgebra K F)) (i : ι) :
    Ideal.Quotient.mk I (coordinates R K F i) = squareGenericCoordinates F I i := rfl

#print axioms evaluation
#print axioms solution
#print axioms jacobian_unit
#print axioms factor_coordinates
end CompleteIncidenceCoordinates
