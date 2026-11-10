import Proposal.SymmetricContactField

noncomputable section
namespace RawContactOpens
open MvPolynomial SymmetricContactField
open scoped BigOperators
set_option maxHeartbeats 2000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false

def coefficient (i : Fin 90) : EqPoly := coefficientValue (fun j => X j) i

theorem eval_coefficient {T : Type*} [CommRing T] [Algebra Base T]
    (x : Index → T) (i : Fin 90) :
    aeval x (coefficient i) = coefficientValue x i := by
  unfold coefficient coefficientValue
  cases h : activeCoordinate i with
  | none => simp
  | some j => simp

theorem seed_coefficient (i : Fin 90) :
    aeval seedPoint (coefficient i) = (coefficientConstant i : ZMod 37) := by
  rw [eval_coefficient]
  fin_cases i <;> decide

def pivot : EqPoly := coefficient 0*coefficient 13-coefficient 6*coefficient 7

def leftNum (j : Fin 7) : EqPoly :=
  coefficient 13*coefficient ⟨j.val,by omega⟩-
    coefficient 6*coefficient ⟨7+j.val,by omega⟩

def rightNum (j : Fin 7) : EqPoly :=
  -coefficient 7*coefficient ⟨j.val,by omega⟩+
    coefficient 0*coefficient ⟨7+j.val,by omega⟩

def deltaX : EqPoly := (rightNum 5)^2-4*rightNum 4*pivot
def deltaY : EqPoly := (rightNum 2)^2-4*rightNum 3*rightNum 1

def AP4num : EqPoly :=
  coefficient 72*pivot-coefficient 71*leftNum 1-coefficient 77*rightNum 1

def BP0num : EqPoly :=
  coefficient 79*pivot-coefficient 78*leftNum 1-coefficient 88*rightNum 1

def pointM0num : EqPoly :=
  pivot+rightNum 5*C (X (1 : Fin 3))+rightNum 4*(C (X (1 : Fin 3)))^2

def pointM2num : EqPoly :=
  rightNum 3+rightNum 2*C (X (2 : Fin 3))+rightNum 1*(C (X (2 : Fin 3)))^2

/-- Additional explicit unit opens; alpha is included separately from the
physical chart coordinate t. -/
def opens : Fin 10 → EqPoly :=
  ![pivot,deltaX,deltaY,rightNum 3,AP4num,BP0num,7,X 71,pointM0num,pointM2num]

def seedValues : Fin 10 → ZMod 37 := ![17,14,22,15,2,14,7,27,16,25]

theorem seed_values (i : Fin 10) : aeval seedPoint (opens i) = seedValues i := by
  fin_cases i <;>
    norm_num [opens,seedValues,pivot,deltaX,deltaY,AP4num,BP0num,
      leftNum,rightNum,pointM0num,pointM2num, seed_coefficient, Matrix.cons_val,Fin.ext_iff,
      coefficientConstant,seedPoint,specialAlgebra,specialMap] <;> decide

theorem seed_opens_unit (i : Fin 10) : IsUnit (aeval seedPoint (opens i)) := by
  rw [seed_values]
  apply isUnit_iff_ne_zero.mpr
  fin_cases i <;> decide

def strengthenedAnchor : EqPoly := anchorPolynomial * ∏ i, opens i

theorem seed_strengthenedAnchor_unit : IsUnit (aeval seedPoint strengthenedAnchor) := by
  rw [strengthenedAnchor,map_mul,map_prod]
  apply seed_anchor_unit.mul
  exact IsUnit.prod_univ_iff.mpr seed_opens_unit

theorem root_anchor_units {T : Type*} [CommRing T] [Algebra Base T]
    (x : Index → T) (h : IsUnit (aeval x strengthenedAnchor)) :
    IsUnit (aeval x normMinorPolynomial) ∧
      IsUnit (aeval x pointAmbientMinorPolynomial) ∧
      ∀ i, IsUnit (aeval x (opens i)) := by
  rw [strengthenedAnchor,map_mul,anchorPolynomial,map_mul,map_prod] at h
  rcases (Commute.all _ _).isUnit_mul_iff.mp h with ⟨h0,h1⟩
  rcases (Commute.all _ _).isUnit_mul_iff.mp h0 with ⟨hn,hp⟩
  exact ⟨hn,hp,IsUnit.prod_univ_iff.mp h1⟩

#print axioms seed_values
#print axioms seed_strengthenedAnchor_unit
#print axioms root_anchor_units
end RawContactOpens
