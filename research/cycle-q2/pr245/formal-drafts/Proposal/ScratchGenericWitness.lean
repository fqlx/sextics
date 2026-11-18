import Mathlib.Algebra.MvPolynomial.Eval
import Mathlib.RingTheory.FiniteType
import Proposal.GeometricMonicWeightedPrimitiveIdentity
import Mathlib.Algebra.MvPolynomial.Rename

/-! Descent of the coefficients of a finite polynomial witness and a unit detecting
a nonzero polynomial after every specialization of those coefficients. -/

set_option autoImplicit false
noncomputable section
namespace CycleQ2FiniteWitness
open MvPolynomial

variable {K E : Type*} [Field K] [Field E] [Algebra K E]
universe u
variable {ι : Type*} {σ τ : Type u} [Fintype ι]

theorem finite_coefficient_model (p : ι → MvPolynomial σ E) (q : MvPolynomial τ E)
    (m : τ →₀ ℕ) (hm : q.coeff m ≠ 0) :
    ∃ (B : Subalgebra K E) (_ : Algebra.FiniteType K B)
      (pB : ι → MvPolynomial σ B) (qB : MvPolynomial τ B),
      (∀ i, MvPolynomial.map B.val.toRingHom (pB i) = p i) ∧
      MvPolynomial.map B.val.toRingHom qB = q ∧ IsUnit (qB.coeff m) := by
  classical
  let S : Finset E := insert (q.coeff m)⁻¹
    ((Finset.univ.biUnion (fun i => (p i).coeffs)) ∪ q.coeffs)
  let B := Algebra.adjoin K (S : Set E)
  have inB {x : E} (hx : x ∈ S) : x ∈ B := Algebra.subset_adjoin hx
  have lift {ρ : Type u} (g : MvPolynomial ρ E) (hg : ∀ x ∈ g.coeffs, x ∈ S) :
      ∃ gB : MvPolynomial ρ B, MvPolynomial.map B.val.toRingHom gB = g := by
    apply MvPolynomial.mem_range_map_iff_coeffs_subset.mpr
    intro x hx
    exact ⟨⟨x,inB (hg x hx)⟩,rfl⟩
  have p_mem (i : ι) (x : E) (hx : x ∈ (p i).coeffs) : x ∈ S := by
    apply Finset.mem_insert_of_mem
    apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ i,hx⟩
  have q_mem (x : E) (hx : x ∈ q.coeffs) : x ∈ S :=
    Finset.mem_insert_of_mem (Finset.mem_union_right _ hx)
  choose pB hpB using fun (i : ι) => lift (p i) (p_mem i)
  obtain ⟨qB,hqB⟩ := lift q q_mem
  refine ⟨B, Algebra.FiniteType.adjoin_of_finite S.finite_toSet, pB, qB, hpB, hqB, ?_⟩
  let y : B := ⟨(q.coeff m)⁻¹,inB (Finset.mem_insert_self _ _)⟩
  refine isUnit_iff_exists_inv.mpr ⟨y,?_⟩
  apply Subtype.ext
  change B.val.toRingHom (qB.coeff m) * (q.coeff m)⁻¹ = 1
  rw [← MvPolynomial.coeff_map, hqB, mul_inv_cancel₀ hm]

end CycleQ2FiniteWitness

#print axioms CycleQ2FiniteWitness.finite_coefficient_model

/-! A rational divergence witness over a large field is defined over a finite
type subalgebra. A coefficient of a spatial multiple of the denominator is
a unit there and remains nonzero in every field specialization. -/

set_option autoImplicit false
noncomputable section
namespace CycleQ2FiniteWitness
open MvPolynomial CycleQ2MonicWeightedPrimitiveIdentity

abbrev Spatial (R : Type*) [CommRing R] := MvPolynomial (Fin 3) R

/-- All identities here are polynomial identities over the coefficient field.
The second one witnesses that `den` divides a nonzero spatial polynomial
in the cubic quotient. -/
structure Certificate (R : Type*) [CommRing R] (f : Pol R) where
  den : Pol R
  num : Fin 3 → Pol R
  spatial : Spatial R
  primitiveFactor : Pol R
  spatialFactor : Pol R
  equationFactor : Pol R
  exponent : Fin 3 →₀ ℕ
  primitive_eq : cleared f den num = f * primitiveFactor
  spatial_eq : rename Fin.castSucc spatial = den * spatialFactor + f * equationFactor
  spatial_unit : IsUnit (spatial.coeff exponent)

theorem descend_cleared {K E : Type*} [Field K] [Field E] [Algebra K E]
    (f : Pol K) (c : Certificate E (MvPolynomial.map (algebraMap K E) f)) :
    ∃ (B : Subalgebra K E) (_ : Algebra.FiniteType K B)
      (cB : Certificate B (MvPolynomial.map (algebraMap K B) f)),
      MvPolynomial.map B.val.toRingHom cB.den = c.den ∧
      (∀ j, MvPolynomial.map B.val.toRingHom (cB.num j) = c.num j) ∧
      MvPolynomial.map B.val.toRingHom cB.spatial = c.spatial := by
  classical
  let P : Fin 4 ⊕ Fin 3 → Pol E :=
    Sum.elim ![c.den,c.primitiveFactor,c.spatialFactor,c.equationFactor] c.num
  obtain ⟨B, hB, P', q', hp, hq, hunit⟩ :=
    finite_coefficient_model (K := K) P c.spatial c.exponent c.spatial_unit.ne_zero
  let i := B.val.toRingHom
  let fB := MvPolynomial.map (algebraMap K B) f
  have hf : MvPolynomial.map i fB = MvPolynomial.map (algebraMap K E) f := by
    change MvPolynomial.map i (MvPolynomial.map (algebraMap K B) f) = _
    rw [MvPolynomial.map_map] <;> rfl
  have hinj : Function.Injective (MvPolynomial.map (σ := Fin 4) i) :=
    MvPolynomial.map_injective i Subtype.val_injective
  have hnum : (fun j => MvPolynomial.map i (P' (.inr j))) = c.num :=
    funext (fun j => hp (.inr j))
  refine ⟨B,hB,⟨P' (.inl 0), fun j => P' (.inr j), q', P' (.inl 1),
    P' (.inl 2), P' (.inl 3), c.exponent, ?_, ?_, hunit⟩,hp (.inl 0),
    fun j => hp (.inr j),hq⟩
  · apply hinj
    change MvPolynomial.map i (cleared fB _ _) = _
    rw [map_cleared, map_mul, hf, hnum, hp (.inl 0), hp (.inl 1)]
    exact c.primitive_eq
  · apply hinj
    rw [map_rename, hq, map_add, map_mul, map_mul, hf, hp (.inl 0), hp (.inl 2), hp (.inl 3)]
    exact c.spatial_eq

/-- Reduction of the descended certificate along any coefficient homomorphism
preserves the two factorizations and nonvanishing of the spatial multiple. -/
def Certificate.map {A B : Type*} [CommRing A] [CommRing B] {f : Pol A}
    (c : Certificate A f) (φ : A →+* B) : Certificate B (MvPolynomial.map φ f) where
  den := MvPolynomial.map φ c.den
  num j := MvPolynomial.map φ (c.num j)
  spatial := MvPolynomial.map φ c.spatial
  primitiveFactor := MvPolynomial.map φ c.primitiveFactor
  spatialFactor := MvPolynomial.map φ c.spatialFactor
  equationFactor := MvPolynomial.map φ c.equationFactor
  exponent := c.exponent
  primitive_eq := by rw [← map_cleared, c.primitive_eq, map_mul]
  spatial_eq := by rw [← map_rename, c.spatial_eq, map_add, map_mul, map_mul]
  spatial_unit := by rw [MvPolynomial.coeff_map]; exact c.spatial_unit.map φ

theorem Certificate.spatial_ne_zero {A : Type*} [CommRing A] [Nontrivial A] {f : Pol A}
    (c : Certificate A f) : c.spatial ≠ 0 := by
  intro h
  apply c.spatial_unit.ne_zero
  rw [h, coeff_zero]

end CycleQ2FiniteWitness
#print axioms CycleQ2FiniteWitness.descend_cleared
#print axioms CycleQ2FiniteWitness.Certificate.map
