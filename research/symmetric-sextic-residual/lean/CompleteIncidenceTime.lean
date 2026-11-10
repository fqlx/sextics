import EtaleDerivationUnique
import CompleteIncidenceCoordinates

noncomputable section
namespace CompleteIncidenceCoordinates
open HoldoutConstruction
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false
variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
variable {ι : Type*} [Fintype ι]

/-- Any derivation killing the parameter ring kills the entire localized
incidence-coordinate algebra, independent of the equation coefficients. -/
theorem time_etale (F : ι → MvPolynomial ι R)
    (E : Derivation ℤ (SquareGenericAlgebra K F) (SquareGenericAlgebra K F))
    (comp : ∀ r : R, E (algebraMap R _ r) = 0) (x : SquareEtaleRing F) :
    E (Algebra.TensorProduct.includeRight x) = 0 := by
  let : Algebra.Etale R (SquareEtaleRing F) := square_system_jacobian_etale F
  let : Algebra (SquareEtaleRing F) (SquareGenericAlgebra K F) :=
    Algebra.TensorProduct.rightAlgebra (R := R) (A := K) (B := SquareEtaleRing F)
  have h := EtaleDerivationLift.algebraMap_compatible
    (K := R) (A := SquareEtaleRing F) (M := SquareGenericAlgebra K F)
    0 0 E (by simp) (by intro r; simpa using comp r) x
  simp only [Derivation.zero_apply,map_zero] at h
  convert h.symm using 1
  congr 1

theorem time_coordinates (F : ι → MvPolynomial ι R)
    (E : Derivation ℤ (SquareGenericAlgebra K F) (SquareGenericAlgebra K F))
    (comp : ∀ r : R, E (algebraMap R _ r) = 0) (i : ι) :
    E (coordinates R K F i) = 0 := by
  change E (Algebra.TensorProduct.includeRight
    (algebraMap (SquareSystemRing F) (SquareEtaleRing F)
      (Ideal.Quotient.mk _ (MvPolynomial.X i)))) = 0
  exact time_etale R K F E comp _

#print axioms time_etale
#print axioms time_coordinates
end CompleteIncidenceCoordinates
