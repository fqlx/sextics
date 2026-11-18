import Mathlib.Algebra.Algebra.Pi
import Mathlib.RingTheory.FiniteType
import Mathlib.RingTheory.Ideal.MinimalPrime.Localization
import Mathlib.RingTheory.Ideal.MinimalPrime.Noetherian
import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
import Mathlib.RingTheory.Localization.FractionRing
import Mathlib.RingTheory.Noetherian.Basic

/-!
# Finiteness of normalization across the minimal primes

The total fraction ring of a reduced ring embeds in the product of the
fraction fields of its minimal components. Integral elements land in the
product of the component normalizations. Over a Noetherian ring the finite
component normalizations thus bound the integral closure of every subalgebra
of the total fraction ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
noncomputable section
namespace CycleQ2ReducedNormalizationFinite

open scoped nonZeroDivisors

variable (A : Type*) [CommRing A]

local instance prime (p : minimalPrimes A) : p.1.IsPrime := p.2.isPrime

abbrev ComponentRing (p : minimalPrimes A) := A ⧸ p.1
abbrev ComponentField (p : minimalPrimes A) := FractionRing (ComponentRing A p)

private theorem component_denominator (p : minimalPrimes A) (s : A⁰) :
    IsUnit (algebraMap A (ComponentField A p) s) := by
  apply isUnit_iff_ne_zero.mpr
  rw [IsScalarTower.algebraMap_apply A (ComponentRing A p) (ComponentField A p)]
  intro he
  have he' : Ideal.Quotient.mk p.1 s = 0 :=
    (IsFractionRing.injective (ComponentRing A p) (ComponentField A p)) (by simpa using he)
  exact notMem_nonZeroDivisors_of_mem_mem_minimalPrimes
    (Ideal.Quotient.eq_zero_iff_mem.mp he') p.2 s.2

/-- The component fraction maps extend across all non-zero-divisors. -/
def fractionComponent (p : minimalPrimes A) : FractionRing A →ₐ[A] ComponentField A p :=
  IsLocalization.liftAlgHom (f := Algebra.ofId A (ComponentField A p)) (component_denominator A p)

private theorem componentProduct_injective [IsReduced A] :
    Function.Injective (algebraMap A (∀ p : minimalPrimes A, ComponentField A p)) := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hmem : x ∈ sInf (minimalPrimes A) := by
    apply Ideal.mem_sInf.mpr
    intro P hP
    let p : minimalPrimes A := ⟨P, hP⟩
    have h := congrFun hx p
    change algebraMap A (ComponentField A p) x = 0 at h
    rw [IsScalarTower.algebraMap_apply A (ComponentRing A p) (ComponentField A p)] at h
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    exact (IsFractionRing.injective (ComponentRing A p) (ComponentField A p)) (by simpa using h)
  change x ∈ sInf (⊥ : Ideal A).minimalPrimes at hmem
  rw [Ideal.sInf_minimalPrimes] at hmem
  change x ∈ nilradical A at hmem
  rw [nilradical_eq_zero] at hmem
  exact hmem

/-- The minimal-component maps jointly detect elements of the total ring of fractions. -/
theorem fractionComponent_injective [IsReduced A] :
    Function.Injective (AlgHom.pi (fractionComponent A)) := by
  apply (IsLocalization.injective_iff_map_algebraMap_eq A⁰ (AlgHom.pi (fractionComponent A)).toRingHom).mpr
  intro x y
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rw [(IsFractionRing.injective A (FractionRing A)).eq_iff, (componentProduct_injective A).eq_iff]

variable {A} {B : Type*} [CommRing B] [Algebra A B]

/-- Jointly injective component maps suffice for finiteness of integral closure. -/
theorem finite_of_component_embeddings [IsNoetherianRing A]
    (h : ∀ p : minimalPrimes A, Module.Finite (ComponentRing A p)
      (integralClosure (ComponentRing A p) (ComponentField A p)))
    (f : ∀ p : minimalPrimes A, B →ₐ[A] ComponentField A p)
    (hf : Function.Injective (AlgHom.pi f)) : Module.Finite A (integralClosure A B) := by
  let : Finite (minimalPrimes A) := (minimalPrimes.finite_of_isNoetherianRing A).to_subtype
  let N (p : minimalPrimes A) := integralClosure (ComponentRing A p) (ComponentField A p)
  let (p : minimalPrimes A) : Module.Finite A (N p) :=
    letI := h p
    Module.Finite.trans (ComponentRing A p) (N p)
  let g (p : minimalPrimes A) : integralClosure A B →ₐ[A] N p :=
    ((f p).domRestrict (integralClosure A B)).codRestrict ((N p).restrictScalars A)
      (fun x => (x.2.map (f p)).tower_top)
  apply Module.Finite.of_injective (AlgHom.pi g).toLinearMap
  intro x y he
  apply Subtype.ext
  apply hf
  exact funext (fun p => congrArg Subtype.val (congrFun he p))

variable (A)

/-- The normalization of a reduced Noetherian ring is finite whenever all of
its irreducible component rings have finite normalization. -/
theorem finite_integralClosure_of_domainQuotients [IsNoetherianRing A] [IsReduced A]
    (h : ∀ p : minimalPrimes A, Module.Finite (ComponentRing A p)
      (integralClosure (ComponentRing A p) (ComponentField A p))) :
    Module.Finite A (integralClosure A (FractionRing A)) :=
  finite_of_component_embeddings h (fractionComponent A) (fractionComponent_injective A)

/-- The same bound applies to the actual ring of sections once it embeds in
the total fraction ring of the reduced affine chart. -/
theorem finite_integralClosure_of_fraction_embedding [IsNoetherianRing A] [IsReduced A]
    (h : ∀ p : minimalPrimes A, Module.Finite (ComponentRing A p)
      (integralClosure (ComponentRing A p) (ComponentField A p)))
    (f : B →ₐ[A] FractionRing A) (hf : Function.Injective f) :
    Module.Finite A (integralClosure A B) :=
  finite_of_component_embeddings h (fun p => (fractionComponent A p).comp f)
    ((fractionComponent_injective A).comp hf)

universe u

/-- Finiteness of normalization for finite-type domains over a field extends
to every reduced finite-type algebra and every subalgebra of its total
fraction ring. The minimal-prime quotients carry their induced algebras. -/
theorem finiteType_integralClosure_of_fraction_embedding
    (k : Type*) [Field k]
    (domainFinite : ∀ (D : Type u) [CommRing D] [IsDomain D] [Algebra k D]
      [Algebra.FiniteType k D], Module.Finite D (integralClosure D (FractionRing D)))
    (R : Type u) [CommRing R] [IsReduced R] [Algebra k R] [Algebra.FiniteType k R]
    {S : Type*} [CommRing S] [Algebra R S] (f : S →ₐ[R] FractionRing R)
    (hf : Function.Injective f) : Module.Finite R (integralClosure R S) := by
  let : IsNoetherianRing R := Algebra.FiniteType.isNoetherianRing k R
  exact finite_integralClosure_of_fraction_embedding R
    (fun p => domainFinite (ComponentRing R p)) f hf

#print axioms fractionComponent_injective
#print axioms finite_integralClosure_of_domainQuotients
#print axioms finite_integralClosure_of_fraction_embedding
#print axioms finiteType_integralClosure_of_fraction_embedding

end CycleQ2ReducedNormalizationFinite
end
