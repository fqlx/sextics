import Proposal.GeometricCurveCylinderAdjunction

/-!
# Descent of the local curve numerator to Kähler differentials

For a closed curve chart cut out by two equations, the conormal exact
sequence descends any linear map on the restricted ambient differentials
which kills those two equation differentials. This works over singular
curves as well.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2CurveCylinderDifferential

open scoped TensorProduct

variable {P A : Type} [CommRing P] [CommRing A] [Algebra ℂ P] [Algebra ℂ A] [Algebra P A]
  [IsScalarTower ℂ P A] {N : Type} [AddCommGroup N] [Module A N]

def ambientD (A : Type) [CommRing A] [Algebra P A] (x : P) :
    A ⊗[P] KaehlerDifferential ℂ P :=
  (1 : A) ⊗ₜ[P] KaehlerDifferential.D ℂ P x

omit [Algebra ℂ A] [IsScalarTower ℂ P A] in
private theorem base_smul (r : P) (β : KaehlerDifferential ℂ P) :
    (1 : A) ⊗ₜ[P] (r • β) = algebraMap P A r • ((1 : A) ⊗ₜ[P] β) := by
  rw [TensorProduct.tmul_smul]
  exact (IsScalarTower.algebraMap_smul A r _).symm

omit [Algebra ℂ A] [IsScalarTower ℂ P A] in
private theorem ambientD_mul (a b : P) :
    ambientD A (a * b) = algebraMap P A a • ambientD A b + algebraMap P A b • ambientD A a := by
  simp only [ambientD, Derivation.leibniz, TensorProduct.tmul_add, base_smul]

/-- The actual conormal sequence identifies the descended map on every restricted
ambient differential, including at singular points. -/
theorem exists_on_curve (h g : P) (hs : Function.Surjective (algebraMap P A))
    (hi : RingHom.ker (algebraMap P A) = Ideal.span {h, g})
    (n : (A ⊗[P] KaehlerDifferential ℂ P) →ₗ[A] N)
    (hh : n ((1 : A) ⊗ₜ[P] KaehlerDifferential.D ℂ P h) = 0)
    (hg : n ((1 : A) ⊗ₜ[P] KaehlerDifferential.D ℂ P g) = 0) :
    ∃! f : KaehlerDifferential ℂ A →ₗ[A] N, f.comp (KaehlerDifferential.mapBaseChange ℂ P A) = n := by
  let q := KaehlerDifferential.mapBaseChange ℂ P A
  have hq : Function.Surjective q := KaehlerDifferential.mapBaseChange_surjective ℂ P A hs
  have h₀ : algebraMap P A h = 0 := by
    apply RingHom.mem_ker.mp
    rw [hi]
    exact Ideal.subset_span (Set.mem_insert _ _)
  have g₀ : algebraMap P A g = 0 := by
    apply RingHom.mem_ker.mp
    rw [hi]
    exact Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _))
  have hk : LinearMap.ker q ≤ LinearMap.ker n := by
    intro x hx
    obtain ⟨z, rfl⟩ := (KaehlerDifferential.exact_kerCotangentToTensor_mapBaseChange ℂ P A hs x).mp hx
    obtain ⟨u, rfl⟩ := (RingHom.ker (algebraMap P A)).toCotangent_surjective z
    change n (ambientD A (u : P)) = 0
    have hu : (u : P) ∈ Ideal.span ({h, g} : Set P) := hi.le u.property
    obtain ⟨a, b, hab⟩ := Ideal.mem_span_pair.mp hu
    have hadd : ambientD A (a * h + b * g) = ambientD A (a * h) + ambientD A (b * g) := by
      simp only [ambientD, map_add, TensorProduct.tmul_add]
    rw [← hab, hadd, ambientD_mul, ambientD_mul, h₀, g₀, zero_smul, zero_smul,
      add_zero, add_zero, map_add, map_smul, map_smul]
    change algebraMap P A a • n ((1 : A) ⊗ₜ[P] KaehlerDifferential.D ℂ P h) +
      algebraMap P A b • n ((1 : A) ⊗ₜ[P] KaehlerDifferential.D ℂ P g) = 0
    rw [hh, hg, smul_zero, smul_zero, zero_add]
  let f := ((LinearMap.ker q).liftQ n hk).comp (q.quotKerEquivOfSurjective hq).symm.toLinearMap
  have hf : f.comp q = n := by
    ext x
    simp only [f, LinearMap.comp_apply, LinearEquiv.coe_coe,
      LinearMap.quotKerEquivOfSurjective_symm_apply, Submodule.liftQ_apply]
  refine ⟨f, hf, ?_⟩
  intro f' hf'
  apply LinearMap.ext
  intro y
  obtain ⟨x, rfl⟩ := hq y
  exact LinearMap.congr_fun (hf'.trans hf.symm) x

open CycleQ2CurveCylinderAdjunction

/-- On a two-equation presentation of the curve this is a linear map on its
genuine sheaf of affine Kähler differentials. Its value on any lifted
ambient one-form is the adjunction numerator with the ordered conormals. -/
theorem exists_adjunction_on_differentials {E : Type} [AddCommGroup E] [Module A E]
    (h g : P) (hs : Function.Surjective (algebraMap P A))
    (hi : RingHom.ker (algebraMap P A) = Ideal.span {h, g})
    (v : (A ⊗[P] KaehlerDifferential ℂ P) →ₗ[A] E) (dt : E) :
    ∃! f : KaehlerDifferential ℂ A →ₗ[A] ⋀[A]^4 E,
      ∀ β : A ⊗[P] KaehlerDifferential ℂ P,
        f (KaehlerDifferential.mapBaseChange ℂ P A β) =
        exteriorPower.ιMulti A 4 ![dt, v (ambientD A h), v (ambientD A g), v β] := by
  let H := v (ambientD A h)
  let G := v (ambientD A g)
  let n := (fibreNumerator (R := A) dt H G).comp ((fibreConormals (R := A) dt H G).mkQ.comp v)
  have hval (β : A ⊗[P] KaehlerDifferential ℂ P) :
      n β = exteriorPower.ιMulti A 4 ![dt, H, G, v β] :=
    fibreNumerator_mk dt H G (v β)
  have hh : n (ambientD A h) = 0 := (hval _).trans
    ((exteriorPower.ιMulti A 4).map_eq_zero_of_eq _ (i := 1) (j := 3) rfl (by decide))
  have hg : n (ambientD A g) = 0 := (hval _).trans
    ((exteriorPower.ιMulti A 4).map_eq_zero_of_eq _ (i := 2) (j := 3) rfl (by decide))
  obtain ⟨f, hf, huniq⟩ := exists_on_curve h g hs hi n hh hg
  refine ⟨f, fun β => (LinearMap.congr_fun hf β).trans (hval β), ?_⟩
  intro f' hf'
  exact huniq f' (LinearMap.ext fun β => (hf' β).trans (hval β).symm)

end CycleQ2CurveCylinderDifferential
end

#print axioms CycleQ2CurveCylinderDifferential.exists_on_curve

#print axioms CycleQ2CurveCylinderDifferential.exists_adjunction_on_differentials
