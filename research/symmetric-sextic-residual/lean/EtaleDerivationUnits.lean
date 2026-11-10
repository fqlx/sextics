import EtaleDerivationUnique
import Mathlib.RingTheory.Ideal.Nonunits

noncomputable section
namespace EtaleDerivationLift
open HoldoutConstruction
set_option maxHeartbeats 4000000
variable {K A : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Algebra.FormallyUnramified K A] [Module.Finite K A]

theorem maximal_derivation_stable (D : Derivation ℤ K K) (E : Derivation ℤ A A)
    (comp : ∀ k, E (algebraMap K A k) = algebraMap K A (D k))
    (I : Ideal A) [I.IsMaximal] {x : A} (hx : x ∈ I) : E x ∈ I := by
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  let F : Derivation ℤ (A ⧸ I) (A ⧸ I) := extendFiniteDerivation D
  have h := algebraMap_compatible D E F comp (extendFiniteDerivation_apply D) x
  apply Ideal.Quotient.eq_zero_iff_mem.mp
  change algebraMap A (A ⧸ I) (E x) = 0
  rw [h]
  have hx0 : algebraMap A (A ⧸ I) x = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr hx
  rw [hx0,map_zero]

/-- A quadratic moving pole is invertible in the entire finite unramified
algebra when its time coordinate has derivative one and its point is constant. -/
theorem moving_square_unit (D : Derivation ℤ K K) (E : Derivation ℤ A A)
    (comp : ∀ k, E (algebraMap K A k) = algebraMap K A (D k))
    (t a : A) (ht : E t = 1) (ha : E a = 0) : IsUnit (t^2-a^2) := by
  by_contra hunit
  obtain ⟨I,hI,hm⟩ := exists_max_ideal_of_mem_nonunits (mem_nonunits_iff.mpr hunit)
  let := hI
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  let : CharZero (A ⧸ I) :=
    charZero_of_injective_ringHom (f := algebraMap K (A ⧸ I))
      (algebraMap K (A ⧸ I)).injective
  have htwo : E (E (t^2-a^2)) = 2 := by
    simp only [pow_two,map_sub,Derivation.leibniz,ht,ha,
      smul_eq_mul,mul_one,mul_zero,map_add,map_zero]
    ring
  have hmem : E (E (t^2-a^2)) ∈ I :=
    maximal_derivation_stable D E comp I (maximal_derivation_stable D E comp I hm)
  rw [htwo] at hmem
  have hzero : (2 : A ⧸ I) = 0 := by
    have h := Ideal.Quotient.eq_zero_iff_mem.mpr hmem
    change Ideal.Quotient.mk I (2 : A) = 0 at h
    rw [map_ofNat] at h
    exact h
  exact (by norm_num : (2 : A ⧸ I) ≠ 0) hzero

#print axioms maximal_derivation_stable
#print axioms moving_square_unit
end EtaleDerivationLift
