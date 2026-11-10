import OpenSquareLift
import RawContactOpens

noncomputable section
namespace StrengthenedContactCover
open MvPolynomial SymmetricAffineField SymmetricRatioCurrent
open HoldoutConstruction ReflectionCoupledFano WeightedPrimitiveTransport
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false

abbrev OriginalIndex := SymmetricContactField.Index
abbrev Index := OriginalIndex ⊕ Unit

def equations : Index → MvPolynomial Index SymmetricContactField.Base :=
  OpenSquareLift.equations SymmetricContactField.equations RawContactOpens.strengthenedAnchor

def seed : Index → ZMod 37 :=
  OpenSquareLift.seed SymmetricContactField.seedPoint RawContactOpens.strengthenedAnchor

theorem exists_field :
    ∃ I : Ideal (SquareGenericAlgebra FunctionField equations), I.IsMaximal ∧
      Module.Finite FunctionField ((SquareGenericAlgebra FunctionField equations) ⧸ I) ∧
      Algebra.IsSeparable FunctionField ((SquareGenericAlgebra FunctionField equations) ⧸ I) ∧
      (∀ i, aeval (squareGenericCoordinates equations I) (equations i) = 0) ∧
      IsUnit (Matrix.det (fun i j => aeval
        (squareGenericCoordinates equations I) (pderiv i (equations j)))) := by
  exact OpenSquareLift.exists_field_with_unit
    SymmetricContactField.equations RawContactOpens.strengthenedAnchor
    SymmetricContactField.seedPoint SymmetricContactField.seed_equations
    SymmetricContactField.seed_jacobian_unit RawContactOpens.seed_strengthenedAnchor_unit
    SymmetricRatioCurrent.parameterMap_injective

abbrev GenericIncidence := SquareGenericAlgebra FunctionField equations
instance (priority := 2000) genericIncidence_module : Module FunctionField GenericIncidence :=
  Algebra.toModule
instance (priority := 2000) genericIncidence_smul : SMul FunctionField GenericIncidence :=
  genericIncidence_module.toSMul

def factor : Ideal GenericIncidence := Classical.choose exists_field
instance factor_maximal : factor.IsMaximal := (Classical.choose_spec exists_field).1
abbrev LiftedField := GenericIncidence ⧸ factor
instance liftedField_field : Field LiftedField := Ideal.Quotient.field factor
instance (priority := 2000) liftedField_module : Module FunctionField LiftedField := Algebra.toModule
instance (priority := 2000) liftedField_smul : SMul FunctionField LiftedField := liftedField_module.toSMul
instance liftedField_finite : Module.Finite FunctionField LiftedField :=
  (Classical.choose_spec exists_field).2.1
instance liftedField_separable : Algebra.IsSeparable FunctionField LiftedField :=
  (Classical.choose_spec exists_field).2.2.1
instance liftedField_charZero : CharZero LiftedField :=
  charZero_of_injective_ringHom (f := algebraMap FunctionField LiftedField)
    (algebraMap FunctionField LiftedField).injective
instance liftedField_parameterAlgebra : Algebra SymmetricContactField.Base LiftedField :=
  ((algebraMap FunctionField LiftedField).comp SymmetricRatioCurrent.parameterMap).toAlgebra
instance (priority := 2000) liftedField_parameterModule : Module SymmetricContactField.Base LiftedField := Algebra.toModule
instance (priority := 2000) liftedField_parameterSMul : SMul SymmetricContactField.Base LiftedField :=
  liftedField_parameterModule.toSMul
instance liftedField_parameterTower : IsScalarTower SymmetricContactField.Base FunctionField LiftedField :=
  IsScalarTower.of_algebraMap_eq (fun _ => rfl)

def augmentedCoordinates : Index → LiftedField := squareGenericCoordinates equations factor

def coordinates (i : OriginalIndex) : LiftedField := augmentedCoordinates (Sum.inl i)

def parameters (i : Fin 3) : LiftedField :=
  algebraMap FunctionField LiftedField (SymmetricRatioCurrent.parameterCoordinates i)

@[simp] theorem parameter (i : Fin 3) :
    algebraMap SymmetricContactField.Base LiftedField (X i) = parameters i := by
  change algebraMap FunctionField LiftedField (SymmetricRatioCurrent.parameterMap (X i)) = _
  rw [SymmetricRatioCurrent.parameterMap_X]
  rfl

theorem augmented_equations (i : Index) : aeval augmentedCoordinates (equations i) = 0 :=
  squareGeneric_solution equations factor i

theorem original_equations (i : OriginalIndex) :
    aeval coordinates (SymmetricContactField.equations i) = 0 :=
  OpenSquareLift.root_original SymmetricContactField.equations
    RawContactOpens.strengthenedAnchor augmentedCoordinates augmented_equations i

theorem anchor_unit : IsUnit (aeval coordinates RawContactOpens.strengthenedAnchor) :=
  OpenSquareLift.root_unit SymmetricContactField.equations
    RawContactOpens.strengthenedAnchor augmentedCoordinates augmented_equations

theorem normMinor_unit : IsUnit (aeval coordinates SymmetricContactField.normMinorPolynomial) :=
  (RawContactOpens.root_anchor_units coordinates anchor_unit).1

theorem pointAmbient_unit : IsUnit (aeval coordinates SymmetricContactField.pointAmbientMinorPolynomial) :=
  (RawContactOpens.root_anchor_units coordinates anchor_unit).2.1

theorem opens_unit (i : Fin 10) : IsUnit (aeval coordinates (RawContactOpens.opens i)) :=
  (RawContactOpens.root_anchor_units coordinates anchor_unit).2.2 i

theorem pivot_nonzero : aeval coordinates RawContactOpens.pivot ≠ 0 :=
  (opens_unit 0).ne_zero

theorem alpha_nonzero : coordinates 71 ≠ 0 := by
  have h := (opens_unit 7).ne_zero
  change aeval coordinates (X (71 : OriginalIndex)) ≠ 0 at h
  simpa using h

theorem original_values (i : OriginalIndex) :
    SymmetricContactField.polynomialValue parameters coordinates
      (SymmetricContactField.equationData i) = 0 := by
  have h := original_equations i
  change aeval coordinates (SymmetricContactField.polynomial (SymmetricContactField.equationData i)) = 0 at h
  rw [SymmetricContactField.eval_polynomial] at h
  simpa only [parameter] using h

theorem norm_identity (y : Fin 5 → LiftedField) :
    7*SymmetricContactField.normValue coordinates y =
      SymmetricContactField.integerTarget (parameters 0) y := by
  have h := SymmetricContactField.norm_identity parameters coordinates y
  simpa [original_values,sub_eq_zero] using h

def point : Fin 5 → LiftedField := SymmetricContactField.pointCoordinates parameters coordinates

theorem contact_point :
    SymmetricContactField.factorValue 0 coordinates point = 0 ∧
    SymmetricContactField.factorValue 1 coordinates point = 0 ∧
    SymmetricContactField.factorValue 4 coordinates point+
      SymmetricContactField.factorValue 5 coordinates point = 0 := by
  refine ⟨?_,?_,?_⟩
  · exact (SymmetricContactField.point_equation_first parameters coordinates).symm.trans (original_values 70)
  · exact (SymmetricContactField.point_equation_second parameters coordinates).symm.trans (original_values 71)
  · exact (SymmetricContactField.point_equation_third parameters coordinates).symm.trans (original_values 72)

#print axioms exists_field
#print axioms pivot_nonzero
#print axioms alpha_nonzero
#print axioms norm_identity
#print axioms contact_point
end StrengthenedContactCover
