import Proposal.ScratchLogarithmicDifferential
import Mathlib.RingTheory.Kaehler.Polynomial
import Mathlib.RingTheory.Etale.Kaehler
import Mathlib.RingTheory.Localization.FractionRing

/-! The exact ambient frame on a localization of a polynomial chart. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2LogPolynomialFrame
open Module CycleQ2LogarithmicDifferential
variable {k : Type} [CommRing k] (I A : Type) [CommRing A] [Algebra k A]
  [Algebra (MvPolynomial I k) A] [IsScalarTower k (MvPolynomial I k) A]

def etaleBasis [Algebra.FormallyEtale (MvPolynomial I k) A] :
    Basis I A (KaehlerDifferential k A) :=
  ((KaehlerDifferential.mvPolynomialBasis k I).baseChange A).map
    (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale k (MvPolynomial I k) A)

theorem etaleBasis_apply [Algebra.FormallyEtale (MvPolynomial I k) A] (i : I) :
    etaleBasis I A i =
      KaehlerDifferential.D k A (algebraMap (MvPolynomial I k) A (MvPolynomial.X i)) := by
  simp only [etaleBasis, Basis.map_apply, Basis.baseChange_apply,
    KaehlerDifferential.mvPolynomialBasis_apply]
  change KaehlerDifferential.mapBaseChange k (MvPolynomial I k) A _ = _
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D]

variable (S : Submonoid (MvPolynomial I k)) [IsLocalization S A]

def localizedBasis : Basis I A (KaehlerDifferential k A) := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := A) S
  exact etaleBasis I A

theorem localizedBasis_apply (i : I) :
    localizedBasis I A S i = KaehlerDifferential.D k A
      (algebraMap (MvPolynomial I k) A (MvPolynomial.X i)) := by
  letI := Algebra.FormallyEtale.of_isLocalization (Rₘ := A) S
  exact etaleBasis_apply I A i

variable [Fintype I] [LinearOrder I]
theorem ambient_commute (i j : I) (v : A) :
    coordDeriv (localizedBasis I A S) i (coordDeriv (localizedBasis I A S) j v) =
      coordDeriv (localizedBasis I A S) j (coordDeriv (localizedBasis I A S) i v) :=
  partials_commute _ _ (localizedBasis_apply I A S) i j v

theorem coordDeriv_polynomial (i : I) (p : MvPolynomial I k) :
    coordDeriv (localizedBasis I A S) i (algebraMap (MvPolynomial I k) A p) =
      algebraMap (MvPolynomial I k) A (MvPolynomial.pderiv i p) := by
  let δ := coordDeriv (localizedBasis I A S) i
  induction p using MvPolynomial.induction_on with
  | C a =>
    have h : algebraMap (MvPolynomial I k) A (MvPolynomial.C a) = algebraMap k A a :=
      (IsScalarTower.algebraMap_apply k (MvPolynomial I k) A a).symm
    rw [h, Derivation.map_algebraMap, MvPolynomial.pderiv_C, map_zero]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p j hp =>
    change δ _ = _
    have hj : δ (algebraMap (MvPolynomial I k) A (MvPolynomial.X j)) = if j = i then 1 else 0 :=
      coordDeriv_coordinate _ _ (localizedBasis_apply I A S) i j
    rw [map_mul, Derivation.leibniz, hj, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_X,
      map_add, map_mul, map_mul]
    change δ (algebraMap (MvPolynomial I k) A p) = _ at hp
    rw [hp]
    by_cases hi : j = i <;> simp [hi, Pi.single_apply, eq_comm, smul_eq_mul, add_comm, mul_comm]

end CycleQ2LogPolynomialFrame
end
#print axioms CycleQ2LogPolynomialFrame.coordDeriv_polynomial
#print axioms CycleQ2LogPolynomialFrame.ambient_commute
