import Mathlib.RingTheory.Etale.Field
import HodgeComputer.Constructions.HoldoutCover.FiniteDifferentials

noncomputable section
namespace EtaleDerivationLift
open HoldoutConstruction
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384

variable {I : Type*} {B : I → Type*} [∀ i, CommRing (B i)]

def product (E : ∀ i, Derivation ℤ (B i) (B i)) :
    Derivation ℤ (∀ i, B i) (∀ i, B i) :=
  Derivation.mk' (LinearMap.pi (fun i => (E i).toLinearMap.comp (LinearMap.proj i))) (by
    intro x y
    funext i
    exact (E i).leibniz (x i) (y i))

@[simp] theorem product_apply (E : ∀ i, Derivation ℤ (B i) (B i)) (x : ∀ i, B i) (i : I) :
    product E x i = E i (x i) := rfl

variable {A C : Type*} [CommRing A] [CommRing C]

def transport (e : A ≃+* C) (E : Derivation ℤ C C) : Derivation ℤ A A :=
  Derivation.mk' (e.symm.toAddMonoidHom.toIntLinearMap ∘ₗ E.toLinearMap ∘ₗ
    e.toAddMonoidHom.toIntLinearMap) (by simp)

@[simp] theorem transport_apply (e : A ≃+* C) (E : Derivation ℤ C C) (x : A) :
    transport e E x = e.symm (E (e x)) := rfl

theorem transport_commute (e : A ≃+* C) (E F : Derivation ℤ C C)
    (h : Function.Commute E F) : Function.Commute (transport e E) (transport e F) := by
  intro x
  simp only [transport_apply, e.apply_symm_apply]
  rw [h]

variable {K : Type*} [Field K] [CharZero K] [Algebra K A] [Algebra.Etale K A]

/-- Every family of base derivations has compatible lifts to a finite étale
algebra, constructed on one complete product decomposition. Commuting pairs
remain commuting. No individual field component is selected. -/
theorem exists_family {κ : Type*} (D : κ → Derivation ℤ K K) :
    ∃ E : κ → Derivation ℤ A A,
      (∀ i k, E i (algebraMap K A k) = algebraMap K A (D i k)) ∧
      (∀ i j, Function.Commute (D i) (D j) → Function.Commute (E i) (E j)) := by
  obtain ⟨I,hI,B,hB,hAlg,e,hfin⟩ :=
    (Algebra.Etale.iff_exists_algEquiv_prod K A).mp inferInstance
  let := hI
  let (i : I) : Field (B i) := hB i
  let (i : I) : Algebra K (B i) := hAlg i
  let (i : I) : Module.Finite K (B i) := (hfin i).1
  let P (i : κ) : Derivation ℤ (∀ j, B j) (∀ j, B j) :=
    product (fun j => extendFiniteDerivation (L := B j) (D i))
  let E (i : κ) : Derivation ℤ A A := transport e.toRingEquiv (P i)
  refine ⟨E, ?_, ?_⟩
  · intro i k
    change e.symm (P i (e (algebraMap K A k))) = algebraMap K A (D i k)
    rw [e.commutes]
    have hp : P i (algebraMap K (∀ j, B j) k) =
        algebraMap K (∀ j, B j) (D i k) := by
      funext j
      exact extendFiniteDerivation_apply (D i) k
    rw [hp,e.symm.commutes]
  · intro i j hc
    apply transport_commute
    intro x
    funext q
    exact extendFiniteDerivation_commute (L := B q) (D i) (D j) hc (x q)

#print axioms exists_family
end EtaleDerivationLift
