import EtaleCanonicalFactorTrace

noncomputable section
namespace EtaleDerivationLift
open HoldoutConstruction
set_option maxHeartbeats 4000000
variable (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [IsArtinianRing A] [IsReduced A]

/-- Assemble a family on EVERY maximal field factor into the complete algebra. -/
def fromFields (x : ∀ m : MaximalSpectrum A, A ⧸ m.asIdeal) : A :=
  (factorEquiv K A).symm x

@[simp] theorem fromFields_component
    (x : ∀ m : MaximalSpectrum A, A ⧸ m.asIdeal) (m : MaximalSpectrum A) :
    Ideal.Quotient.mk m.asIdeal (fromFields K A x) = x m := by
  have h := congrArg (fun y : ∀ m : MaximalSpectrum A, A ⧸ m.asIdeal => y m)
    ((factorEquiv K A).apply_symm_apply x)
  exact h

variable [Module.Finite K A] [Fintype (MaximalSpectrum A)]
local instance assembly_factor_field (m : MaximalSpectrum A) : Field (A ⧸ m.asIdeal) :=
  Ideal.Quotient.field _

theorem trace_fromFields (x : ∀ m : MaximalSpectrum A, A ⧸ m.asIdeal) :
    Algebra.trace K A (fromFields K A x) =
      ∑ m : MaximalSpectrum A, Algebra.trace K (A ⧸ m.asIdeal) (x m) := by
  rw [trace_all_factors]
  simp only [fromFields_component]

variable [CharZero K] [Algebra.FormallyUnramified K A]

omit [Fintype (MaximalSpectrum A)] in
/-- The assembled current satisfies its assembled source equation as soon as
this is verified on every maximal field factor. -/
theorem divergence_fromFields {ι : Type*} [Fintype ι]
    (D : ι → Derivation ℤ K K) (E : ι → Derivation ℤ A A)
    (comp : ∀ i k, E i (algebraMap K A k) = algebraMap K A (D i k))
    (w : ∀ m : MaximalSpectrum A, ι → A ⧸ m.asIdeal)
    (source : ∀ m : MaximalSpectrum A, A ⧸ m.asIdeal)
    (equations : ∀ m : MaximalSpectrum A,
      (∑ i, extendFiniteDerivation (L := A ⧸ m.asIdeal) (D i) (w m i)) = source m) :
    (∑ i, E i (fromFields K A (fun m => w m i))) = fromFields K A source := by
  apply divergence_of_all_maximal_quotients D E comp
  intro I hI
  let := hI
  let : Field (A ⧸ I) := Ideal.Quotient.field I
  let m : MaximalSpectrum A := ⟨I,hI⟩
  change (∑ i, extendFiniteDerivation (L := A ⧸ m.asIdeal) (D i)
    (Ideal.Quotient.mk m.asIdeal (fromFields K A (fun m => w m i)))) =
      Ideal.Quotient.mk m.asIdeal (fromFields K A source)
  simp only [fromFields_component]
  exact equations m

#print axioms fromFields
#print axioms fromFields_component
#print axioms trace_fromFields
#print axioms divergence_fromFields
end EtaleDerivationLift
