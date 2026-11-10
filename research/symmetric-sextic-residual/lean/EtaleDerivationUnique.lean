import EtaleDerivationLift

noncomputable section
namespace EtaleDerivationLift
set_option maxHeartbeats 4000000
variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [Algebra.FormallyUnramified K A]

/-- Integer derivations out of an unramified algebra that agree on the base
agree everywhere, also with values in another commutative algebra. -/
theorem derivation_unique {M : Type*} [CommRing M] [Algebra K M] [Algebra A M]
    [IsScalarTower K A M] (E F : Derivation ℤ A M)
    (hbase : ∀ k : K, E (algebraMap K A k) = F (algebraMap K A k)) : E = F := by
  let L : A →ₗ[K] M :=
    { toFun := fun x => E x-F x
      map_add' := by intro x y; simp only [map_add]; abel
      map_smul' := by
        intro k x
        change E (k • x)-F (k • x) = k • (E x-F x)
        simp only [Algebra.smul_def, Derivation.leibniz]
        rw [hbase, ← IsScalarTower.algebraMap_apply K A M]
        ring }
  let d : Derivation K A M := Derivation.mk' L (by
    intro x y
    change E (x*y)-F (x*y) = x • (E y-F y)+y • (E x-F x)
    simp only [Derivation.leibniz, Algebra.smul_def]
    ring)
  have hs : Subsingleton (Derivation K A M) :=
    (KaehlerDifferential.linearMapEquivDerivation K A).surjective.subsingleton
  have hz : d = 0 := @Subsingleton.elim _ hs d 0
  ext x
  have h := congrArg (fun v : Derivation K A M => v x) hz
  change E x-F x = 0 at h
  exact sub_eq_zero.mp h

theorem endomorphism_unique (E F : Derivation ℤ A A)
    (hbase : ∀ k : K, E (algebraMap K A k) = F (algebraMap K A k)) : E = F :=
  derivation_unique E F hbase

/-- Every algebra map from the unramified algebra to another differential
algebra is automatically compatible once both derivations lift the same base. -/
theorem algebraMap_compatible {M : Type*} [CommRing M] [Algebra K M] [Algebra A M]
    [IsScalarTower K A M] (D : Derivation ℤ K K)
    (E : Derivation ℤ A A) (F : Derivation ℤ M M)
    (compE : ∀ k, E (algebraMap K A k) = algebraMap K A (D k))
    (compF : ∀ k, F (algebraMap K M k) = algebraMap K M (D k)) (x : A) :
    algebraMap A M (E x) = F (algebraMap A M x) := by
  have h := derivation_unique ((Algebra.linearMap A M).compDer E)
    (F.compAlgebraMap A) (by
      intro k
      change algebraMap A M (E (algebraMap K A k)) =
        F (algebraMap A M (algebraMap K A k))
      simp only [compE, ← IsScalarTower.algebraMap_apply K A M, compF])
  exact congrArg (fun d : Derivation ℤ A M => d x) h

#print axioms derivation_unique
#print axioms endomorphism_unique
#print axioms algebraMap_compatible
end EtaleDerivationLift
