import EtaleDerivationUnits
import TotalIncidenceDerivations

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace ActualTotalIncidence
open SymmetricAffineField SymmetricRatioCurrent HoldoutConstruction
attribute [local irreducible] StrengthenedContactCover.equations SymmetricContactField.equations

theorem moving_map {M : Type*} [CommRing M] [_root_.Algebra FunctionField M] [_root_.Algebra Algebra M]
    [IsScalarTower FunctionField Algebra M] (i : Fin 3) (F : Derivation ℤ M M)
    (compF : ∀ k, F (algebraMap FunctionField M k) =
      algebraMap FunctionField M (ratioTangent i k)) (x : Algebra) :
    algebraMap Algebra M (moving i x) = F (algebraMap Algebra M x) :=
  EtaleDerivationLift.algebraMap_compatible (ratioTangent i) (moving i) F
    (moving_compatible i) compF x

theorem time_base (x : SymmetricContactField.Base) :
    moving 0 (algebraMap SymmetricContactField.Base Algebra x) = 0 := by
  change moving 0 (algebraMap FunctionField Algebra (parameterMap x)) = 0
  rw [moving_compatible,time_parameterMap,map_zero]

theorem time_etale (x : SquareEtaleRing StrengthenedContactCover.equations) :
    moving 0 (Algebra.TensorProduct.includeRight x : Algebra) = 0 := by
  let : Algebra.Etale SymmetricContactField.Base
      (SquareEtaleRing StrengthenedContactCover.equations) :=
    square_system_jacobian_etale StrengthenedContactCover.equations
  let : _root_.Algebra (SquareEtaleRing StrengthenedContactCover.equations) Algebra :=
    _root_.Algebra.TensorProduct.rightAlgebra
      (R := SymmetricContactField.Base) (A := FunctionField)
      (B := SquareEtaleRing StrengthenedContactCover.equations)
  have h := EtaleDerivationLift.algebraMap_compatible
    (K := SymmetricContactField.Base)
    (A := SquareEtaleRing StrengthenedContactCover.equations)
    (M := Algebra) 0 0 (moving 0) (by simp) (by
      intro k
      simpa using time_base k) x
  simp only [Derivation.zero_apply,map_zero] at h
  convert h.symm using 1
  congr 1

theorem time_coordinates (i : StrengthenedContactCover.Index) :
    moving 0 (coordinates i) = 0 := by
  change moving 0 (Algebra.TensorProduct.includeRight
    (algebraMap (SquareSystemRing StrengthenedContactCover.equations)
      (SquareEtaleRing StrengthenedContactCover.equations)
      (Ideal.Quotient.mk _ (MvPolynomial.X i)))) = 0
  exact time_etale _

theorem time_originalCoordinates (i : SymmetricContactField.Index) :
    moving 0 (originalCoordinates i) = 0 := time_coordinates _

theorem time_t : moving 0 (algebraMap FunctionField Algebra t) = 1 := by
  rw [moving_compatible]
  have h : ratioTangent 0 t = 1 := by simpa using ratio_t 0
  rw [h,map_one]

theorem moving_pole_unit :
    IsUnit ((algebraMap FunctionField Algebra t)^2-(originalCoordinates 71)^2) :=
  EtaleDerivationLift.moving_square_unit (ratioTangent 0) (moving 0)
    (moving_compatible 0) _ _ time_t (time_originalCoordinates 71)

#print axioms time_t
#print axioms moving_pole_unit
#print axioms moving_map
#print axioms time_base
#print axioms time_etale
#print axioms time_coordinates
#print axioms time_originalCoordinates
end ActualTotalIncidence
