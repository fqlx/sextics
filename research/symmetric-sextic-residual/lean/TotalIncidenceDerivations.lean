import EtaleDerivationLift
import TotalIncidenceRatioTrace

noncomputable section
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
namespace LocalizedIncidenceTotal
open HoldoutConstruction
variable (R K : Type*) [CommRing R] [Field K] [Algebra R K]
variable {ι : Type*} [Fintype ι]
instance etale (F : ι → MvPolynomial ι R) :
    Algebra.Etale K (SquareGenericAlgebra K F) := by
  let : Algebra.Etale R (SquareEtaleRing F) := square_system_jacobian_etale F
  infer_instance
end LocalizedIncidenceTotal

namespace ActualTotalIncidence
open SymmetricAffineField SymmetricPrimitiveEndpoint SymmetricRatioCurrent
attribute [local irreducible] StrengthenedContactCover.equations SymmetricContactField.equations

theorem ratio_derivations_exist :
    ∃ E : Fin 3 → Derivation ℤ Algebra Algebra,
      (∀ i x, E i (algebraMap FunctionField Algebra x) =
        algebraMap FunctionField Algebra (ratioTangent i x)) ∧
      (∀ i j, Function.Commute (ratioTangent i) (ratioTangent j) →
        Function.Commute (E i) (E j)) :=
  EtaleDerivationLift.exists_family (A := Algebra) ratioTangent

/-- One compatible family on the entire incidence algebra. -/
def moving : Fin 3 → Derivation ℤ Algebra Algebra :=
  Classical.choose ratio_derivations_exist

theorem moving_compatible (i : Fin 3) (x : FunctionField) :
    moving i (algebraMap FunctionField Algebra x) =
      algebraMap FunctionField Algebra (ratioTangent i x) :=
  (Classical.choose_spec ratio_derivations_exist).1 i x

theorem moving_commute_of (i j : Fin 3)
    (h : Function.Commute (ratioTangent i) (ratioTangent j)) :
    Function.Commute (moving i) (moving j) :=
  (Classical.choose_spec ratio_derivations_exist).2 i j h

theorem moving_time_r_commute : Function.Commute (moving 0) (moving 1) :=
  moving_commute_of 0 1 ratio_time_r_commute

theorem moving_time_s_commute : Function.Commute (moving 0) (moving 2) :=
  moving_commute_of 0 2 ratio_time_s_commute

theorem moving_r_s_commute : Function.Commute (moving 1) (moving 2) :=
  moving_commute_of 1 2 SymmetricContactField.ratio_r_s_commute

theorem totalTrace_moving (i : Fin 3) (x : Algebra) :
    totalTrace (moving i x) = ratioTangent i (totalTrace x) :=
  LocalizedIncidenceTotal.trace_derivation SymmetricContactField.Base FunctionField
    StrengthenedContactCover.equations (ratioTangent i) (moving i)
    (moving_compatible i) x

/-- After the compatible commuting lifts have been constructed, the genuine
upstairs current equation and actual total source trace are the only inputs. -/
def relativePrimitiveOfLiftedTotalSource
    (w : Fin 3 → Algebra) (source : Algebra)
    (equation : (∑ i, moving i (w i)) = source)
    (htrace : totalTrace source = -t*residueDensity) : RelativePrimitive :=
  relativePrimitiveOfTotalRatioSource moving moving_compatible w source equation htrace

#print axioms ratio_derivations_exist
#print axioms moving_compatible
#print axioms moving_time_r_commute
#print axioms moving_time_s_commute
#print axioms moving_r_s_commute
#print axioms totalTrace_moving
#print axioms relativePrimitiveOfLiftedTotalSource
end ActualTotalIncidence
