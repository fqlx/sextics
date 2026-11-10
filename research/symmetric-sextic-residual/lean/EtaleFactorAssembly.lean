import EtaleDerivationUnits

noncomputable section
namespace EtaleDerivationLift
open HoldoutConstruction
set_option maxHeartbeats 4000000
variable {K A : Type*} [Field K] [CharZero K] [CommRing A] [Algebra K A]
    [Algebra.FormallyUnramified K A] [Module.Finite K A]

include K in
omit [CharZero K] in
theorem eq_of_all_maximal_quotients {x y : A}
    (h : ∀ (I : Ideal A), I.IsMaximal → Ideal.Quotient.mk I x = Ideal.Quotient.mk I y) : x = y := by
  let : IsArtinianRing A := IsArtinianRing.of_finite K A
  let : IsReduced A := Algebra.FormallyUnramified.isReduced_of_field K A
  apply (IsArtinianRing.equivPi A).injective
  funext m
  exact h m.asIdeal inferInstance

/-- Field-factor equations assemble to an equation in the complete algebra.
Every maximal factor is quantified; a selected partial set is insufficient. -/
theorem divergence_of_all_maximal_quotients {ι : Type*} [Fintype ι]
    (D : ι → Derivation ℤ K K) (E : ι → Derivation ℤ A A)
    (comp : ∀ i k, E i (algebraMap K A k) = algebraMap K A (D i k))
    (w : ι → A) (source : A)
    (h : ∀ (I : Ideal A) (_ : I.IsMaximal),
      letI : Field (A ⧸ I) := Ideal.Quotient.field I
      (∑ i, extendFiniteDerivation (L := A ⧸ I) (D i)
        (Ideal.Quotient.mk I (w i))) = Ideal.Quotient.mk I source) :
    (∑ i, E i (w i)) = source := by
  apply eq_of_all_maximal_quotients (K := K)
  intro I hI
  let := hI
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  rw [map_sum]
  have he (i : ι) : Ideal.Quotient.mk I (E i (w i)) =
      extendFiniteDerivation (L := A ⧸ I) (D i) (Ideal.Quotient.mk I (w i)) :=
    algebraMap_compatible (D i) (E i) (extendFiniteDerivation (D i))
      (comp i) (extendFiniteDerivation_apply (D i)) (w i)
  simp_rw [he]
  exact h I hI

#print axioms eq_of_all_maximal_quotients
#print axioms divergence_of_all_maximal_quotients
end EtaleDerivationLift
