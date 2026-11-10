import FiniteAlgebraTrace
import CompleteIncidenceCoordinates
import StrengthenedContactCover

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
open scoped BigOperators TensorProduct
namespace LocalizedIncidenceTotal
open HoldoutConstruction
variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
variable {ι : Type*} [Fintype ι]

/-- The complete Jacobian-localized generic incidence algebra is finite;
no maximal ideal or irreducible factor is chosen. -/
instance finite (F : ι → MvPolynomial ι R) :
    Module.Finite K (SquareGenericAlgebra K F) := by
  let : Algebra.Etale R (SquareEtaleRing F) := square_system_jacobian_etale F
  exact genericEtale_finite R K (SquareEtaleRing F)

def basis (F : ι → MvPolynomial ι R) :
    Module.Basis (Fin (Module.finrank K (SquareGenericAlgebra K F)))
      K (SquareGenericAlgebra K F) :=
  Module.finBasis K (SquareGenericAlgebra K F)

/-- Complete algebra trace divided by total vector-space rank. -/
def trace (F : ι → MvPolynomial ι R) : SquareGenericAlgebra K F →ₗ[K] K :=
  FiniteAlgebraTrace.averageTrace (basis R K F)

theorem trace_matrix (F : ι → MvPolynomial ι R) (x : SquareGenericAlgebra K F) :
    trace R K F x = (Module.finrank K (SquareGenericAlgebra K F) : K)⁻¹ *
      Matrix.trace (Algebra.leftMulMatrix (basis R K F) x) := by
  simpa only [trace, Fintype.card_fin] using
    FiniteAlgebraTrace.averageTrace_matrix (basis R K F) x

theorem trace_derivation (F : ι → MvPolynomial ι R)
    (D : Derivation ℤ K K) (E : Derivation ℤ (SquareGenericAlgebra K F) (SquareGenericAlgebra K F))
    (comp : ∀ k, E (algebraMap K _ k) = algebraMap K _ (D k)) (x : SquareGenericAlgebra K F) :
    trace R K F (E x) = D (trace R K F x) :=
  FiniteAlgebraTrace.averageTrace_derivation (basis R K F) D E comp x

theorem trace_algebraMap [CharZero K] (F : ι → MvPolynomial ι R)
    [Nontrivial (SquareGenericAlgebra K F)] (k : K) :
    trace R K F (algebraMap K _ k) = k := by
  have hn : (Fintype.card (Fin (Module.finrank K (SquareGenericAlgebra K F))) : K) ≠ 0 := by
    rw [Fintype.card_fin]
    exact Nat.cast_ne_zero.mpr (Nat.ne_of_gt (Module.finrank_pos (R := K)
      (M := SquareGenericAlgebra K F)))
  exact FiniteAlgebraTrace.averageTrace_algebraMap (basis R K F) hn k

theorem trace_divergence (F : ι → MvPolynomial ι R) {κ : Type*} [Fintype κ]
    (D : κ → Derivation ℤ K K)
    (E : κ → Derivation ℤ (SquareGenericAlgebra K F) (SquareGenericAlgebra K F))
    (comp : ∀ i k, E i (algebraMap K _ k) = algebraMap K _ (D i k))
    (w : κ → SquareGenericAlgebra K F) :
    (∑ i, D i (trace R K F (w i))) = trace R K F (∑ i, E i (w i)) :=
  FiniteAlgebraTrace.averageTrace_divergence (basis R K F) D E comp w

/-- A source-trace comparison is still an explicit input. -/
theorem descends_source (F : ι → MvPolynomial ι R) {κ : Type*} [Fintype κ]
    (D : κ → Derivation ℤ K K)
    (E : κ → Derivation ℤ (SquareGenericAlgebra K F) (SquareGenericAlgebra K F))
    (comp : ∀ i k, E i (algebraMap K _ k) = algebraMap K _ (D i k))
    (w : κ → SquareGenericAlgebra K F) (source : SquareGenericAlgebra K F) (r : K)
    (equation : (∑ i, E i (w i)) = source) (htrace : trace R K F source = r) :
    (∑ i, D i (trace R K F (w i))) = r := by
  rw [trace_divergence R K F D E comp, equation, htrace]
end LocalizedIncidenceTotal

namespace ActualTotalIncidence
attribute [local irreducible] StrengthenedContactCover.equations SymmetricContactField.equations
open SymmetricAffineField StrengthenedContactCover
abbrev Algebra := StrengthenedContactCover.GenericIncidence
instance nontrivial : Nontrivial Algebra :=
  (Ideal.Quotient.mk StrengthenedContactCover.factor).domain_nontrivial
instance finite : Module.Finite FunctionField Algebra :=
  LocalizedIncidenceTotal.finite SymmetricContactField.Base FunctionField
    StrengthenedContactCover.equations

def totalTrace : Algebra →ₗ[FunctionField] FunctionField :=
  LocalizedIncidenceTotal.trace SymmetricContactField.Base FunctionField
    StrengthenedContactCover.equations

theorem totalRank_pos : 0 < Module.finrank FunctionField Algebra := Module.finrank_pos

theorem totalTrace_base (x : FunctionField) :
    totalTrace (algebraMap FunctionField Algebra x) = x :=
  LocalizedIncidenceTotal.trace_algebraMap SymmetricContactField.Base FunctionField
    StrengthenedContactCover.equations x


def coordinates : StrengthenedContactCover.Index → Algebra :=
  CompleteIncidenceCoordinates.coordinates SymmetricContactField.Base FunctionField
    StrengthenedContactCover.equations

def originalCoordinates : SymmetricContactField.Index → Algebra :=
  fun i => coordinates (Sum.inl i)

theorem coordinates_equations (i : StrengthenedContactCover.Index) :
    MvPolynomial.aeval coordinates (StrengthenedContactCover.equations i) = 0 :=
  CompleteIncidenceCoordinates.solution SymmetricContactField.Base FunctionField
    StrengthenedContactCover.equations i

theorem coordinates_jacobian_unit :
    IsUnit (Matrix.det (fun i j => MvPolynomial.aeval coordinates
      (MvPolynomial.pderiv i (StrengthenedContactCover.equations j)))) :=
  CompleteIncidenceCoordinates.jacobian_unit SymmetricContactField.Base FunctionField
    StrengthenedContactCover.equations

theorem original_equations (i : SymmetricContactField.Index) :
    MvPolynomial.aeval originalCoordinates (SymmetricContactField.equations i) = 0 := by
  have hs : ∀ j, MvPolynomial.aeval coordinates
      (OpenSquareLift.equations SymmetricContactField.equations
        RawContactOpens.strengthenedAnchor j) = 0 := by
    simpa only [StrengthenedContactCover.equations] using coordinates_equations
  exact OpenSquareLift.root_original SymmetricContactField.equations
    RawContactOpens.strengthenedAnchor coordinates hs i

theorem anchor_unit :
    IsUnit (MvPolynomial.aeval originalCoordinates RawContactOpens.strengthenedAnchor) := by
  have hs : ∀ j, MvPolynomial.aeval coordinates
      (OpenSquareLift.equations SymmetricContactField.equations
        RawContactOpens.strengthenedAnchor j) = 0 := by
    simpa only [StrengthenedContactCover.equations] using coordinates_equations
  exact OpenSquareLift.root_unit SymmetricContactField.equations
    RawContactOpens.strengthenedAnchor coordinates hs

theorem opens_unit (i : Fin 10) :
    IsUnit (MvPolynomial.aeval originalCoordinates (RawContactOpens.opens i)) :=
  (RawContactOpens.root_anchor_units originalCoordinates anchor_unit).2.2 i

theorem pivot_unit : IsUnit (MvPolynomial.aeval originalCoordinates RawContactOpens.pivot) :=
  opens_unit 0

theorem alpha_unit : IsUnit (originalCoordinates 71) := by
  have h := opens_unit 7
  change IsUnit (MvPolynomial.aeval originalCoordinates
    (MvPolynomial.X (71 : SymmetricContactField.Index))) at h
  simpa only [MvPolynomial.aeval_X] using h

theorem selectedFactor_coordinates (i : StrengthenedContactCover.Index) :
    Ideal.Quotient.mk StrengthenedContactCover.factor (coordinates i) =
      StrengthenedContactCover.augmentedCoordinates i :=
  CompleteIncidenceCoordinates.factor_coordinates SymmetricContactField.Base FunctionField
    StrengthenedContactCover.equations StrengthenedContactCover.factor i

/-- This is a direct constructor for the protected primitive from a genuine
complete-algebra current and an explicit total source trace identity. -/
def relativePrimitiveOfTotalSource
    (E : Fin 3 → Derivation ℤ Algebra Algebra)
    (comp : ∀ (i : Fin 3) (x : FunctionField), E i (algebraMap FunctionField Algebra x) =
      algebraMap FunctionField Algebra (SymmetricPrimitiveEndpoint.tangent i.succ x))
    (w : Fin 3 → Algebra) (source : Algebra)
    (equation : (∑ i, E i (w i)) = source)
    (htrace : totalTrace source = SymmetricPrimitiveEndpoint.residueDensity) :
    SymmetricPrimitiveEndpoint.RelativePrimitive where
  coefficient := fun i => totalTrace (w i)
  differential_eq := by
    calc
      _ = ∑ i, totalTrace (E i (w i)) := by
        apply Finset.sum_congr rfl
        intro i _
        exact (LocalizedIncidenceTotal.trace_derivation SymmetricContactField.Base
          FunctionField StrengthenedContactCover.equations
          (SymmetricPrimitiveEndpoint.tangent i.succ) (E i)
          (fun x => comp i x) (w i)).symm
      _ = totalTrace (∑ i, E i (w i)) := (map_sum totalTrace _ _).symm
      _ = _ := by rw [equation,htrace]
end ActualTotalIncidence

#print axioms LocalizedIncidenceTotal.finite
#print axioms LocalizedIncidenceTotal.trace_derivation
#print axioms LocalizedIncidenceTotal.descends_source
#print axioms ActualTotalIncidence.totalRank_pos
#print axioms ActualTotalIncidence.totalTrace_base
#print axioms ActualTotalIncidence.coordinates_equations
#print axioms ActualTotalIncidence.coordinates_jacobian_unit
#print axioms ActualTotalIncidence.opens_unit
#print axioms ActualTotalIncidence.alpha_unit
#print axioms ActualTotalIncidence.selectedFactor_coordinates
#print axioms ActualTotalIncidence.relativePrimitiveOfTotalSource
