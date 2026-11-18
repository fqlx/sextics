import Proposal.ScratchLogCofactor
import Proposal.ScratchLogChartExact

/-!
# Cartan's formula for a weighted coordinate vector field

For a variable vector field, the commutator of exterior differentiation and
contraction has one contribution from differentiating the coefficients of a
form and one from differentiating the coefficients of the vector field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2LogRadialCartan
open CycleQ2LogBasisConnection CycleQ2PoleReductionLocal CycleQ2LogarithmicDifferential
open CycleQ2LiteralThreefoldResidueContraction (interior interior_add)

variable {k R : Type} [CommRing k] [CommRing R] [Algebra k R]
variable {I : Type} [Fintype I] [LinearOrder I]
variable (b : Module.Basis I R (KaehlerDifferential k R))
local notation "d₁" => KaehlerDifferential.D k R

private def interiorLinear {M : Type} [AddCommGroup M] [Module R M] (n : ℕ) :
    (M →ₗ[R] R) →ₗ[R] ((⋀[R]^(n+1) M) →ₗ[R] (⋀[R]^n M)) where
  toFun := interior n
  map_add' := interior_add n
  map_smul' c v := by
    have h : (c • v).smulRight (exteriorPower.ιMulti R n (M := M)) =
        c • v.smulRight (exteriorPower.ιMulti R n (M := M)) := by
      apply LinearMap.ext
      intro x
      simp [smul_smul]
    unfold interior
    simp only [h, AlternatingMap.alternatizeUncurryFin_smul, map_smul, RingHom.id_apply]

/-- The Kähler covector associated to the vector field with coordinates `c`. -/
def covector (c : I → R) : KaehlerDifferential k R →ₗ[R] R :=
  ∑ i, c i • b.coord i

/-- The covector evaluates a universal differential as the corresponding
linear combination of coordinate derivatives. -/
theorem covector_apply_D (c : I → R) (f : R) :
    covector b c (d₁ f) = ∑ i, c i * coordDeriv b i f := by
  simp only [covector, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul] <;> rfl

theorem covector_eq_lift (c : I → R) : covector b c =
    (∑ i, c i • coordDeriv b i).liftKaehlerDifferential := by
  apply Derivation.liftKaehlerDifferential_unique
  rw [Derivation.liftKaehlerDifferential_comp]
  ext f
  change covector b c (d₁ f) = (∑ i, c i • coordDeriv b i) f
  simp only [covector_apply_D, Derivation.sum_apply, Derivation.smul_apply, smul_eq_mul]

/-- Contraction by a vector field, assembled from the coordinate contractions. -/
def weightedInterior (c : I → R) (n : ℕ) : Form k R (n+1) →ₗ[R] Form k R n :=
  ∑ i, c i • interior n (b.coord i)

theorem weightedInterior_eq (c : I → R) (n : ℕ) :
    weightedInterior b c n = interior n (covector b c) := by
  change _ = interiorLinear n (∑ i, c i • b.coord i)
  simp only [map_sum, map_smul] <;> rfl

theorem weightedInterior_apply (c : I → R) (n : ℕ) (ω : Form k R (n+1)) :
    weightedInterior b c n ω = ∑ i, c i • interior n (b.coord i) ω := by
  simp only [weightedInterior, LinearMap.sum_apply, LinearMap.smul_apply]

/-- Cartan's formula on positive-degree forms in a coordinate frame. -/
theorem cartan (c : I → R) (n : ℕ) (ω : Form k R (n+1)) :
    exteriorD b n (interior n (covector b c) ω) +
        interior (n+1) (covector b c) (exteriorD b (n+1) ω) =
      (∑ i, c i • coeffD (b.exteriorPower (n+1)) (coordDeriv b i) ω) +
        ∑ i, prepend n (d₁ (c i)) (interior n (b.coord i) ω) := by
  simp only [← weightedInterior_eq, weightedInterior_apply, map_sum,
    CycleQ2LogChartExact.exteriorD_leibniz_scalar, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i _
  rw [← CycleQ2LogCofactor.cartan b n i ω, smul_add]
  abel

/-- With a diagonal vector field of constant weights the second term acts by
the corresponding exterior degree operator. -/
theorem euler (x w : I → R) (hx : ∀ i, b i = d₁ (x i))
    (hw : ∀ i, d₁ (w i) = 0) (n : ℕ) (ω : Form k R (n+1)) :
    exteriorD b n (interior n (covector b (fun i => w i * x i)) ω) +
        interior (n+1) (covector b (fun i => w i * x i)) (exteriorD b (n+1) ω) =
      (∑ i, (w i * x i) • coeffD (b.exteriorPower (n+1)) (coordDeriv b i) ω) +
        ∑ i, w i • prepend n (b i) (interior n (b.coord i) ω) := by
  rw [cartan]
  simp only [Derivation.leibniz, hw, smul_zero, add_zero, ← hx, CycleQ2LogWedge.prepend_smul]

end CycleQ2LogRadialCartan
end
#print axioms CycleQ2LogRadialCartan.weightedInterior_eq
#print axioms CycleQ2LogRadialCartan.covector_eq_lift
#print axioms CycleQ2LogRadialCartan.cartan
#print axioms CycleQ2LogRadialCartan.euler
