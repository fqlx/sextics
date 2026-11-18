import Proposal.GeometricExteriorSheaf
import Mathlib.LinearAlgebra.ExteriorPower.Basis

/-!
# Pullback of relative differential forms on exact coordinate charts

A differential satisfying the ordinary rule on forms a·df₁∧⋯∧dfₙ
commutes with pullback along every algebra morphism into a second
exact chart. The source and target can have different dimensions.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LogarithmicPullback
open CycleQ2GeometricExteriorSheaf (exteriorMap exteriorMap_wedge)

variable {k R S : Type} [CommRing k] [CommRing R] [CommRing S]
  [Algebra k R] [Algebra k S]
variable (π : R →ₐ[k] S)

/-- Pullback of ordinary relative Kähler differentials to the hypersurface. -/
def differential : KaehlerDifferential k R →ₛₗ[π.toRingHom] KaehlerDifferential k S := by
  letI : Algebra R S := π.toRingHom.toAlgebra
  letI : IsScalarTower k R S := IsScalarTower.of_algHom π
  exact {
    toFun := KaehlerDifferential.map k k R S
    map_add' := map_add _
    map_smul' := fun r x => by
      change KaehlerDifferential.map k k R S (r • x) =
        algebraMap R S r • KaehlerDifferential.map k k R S x
      rw [map_smul, IsScalarTower.algebraMap_smul] }

@[simp] theorem differential_D (r : R) :
    differential π (KaehlerDifferential.D k R r) = KaehlerDifferential.D k S (π r) := by
  letI : Algebra R S := π.toRingHom.toAlgebra
  letI : IsScalarTower k R S := IsScalarTower.of_algHom π
  exact KaehlerDifferential.map_D k k R S r

/-- The semilinear presentation agrees with the Kähler comparison from
a given algebra tower, including towers using other scalar-action instances. -/
theorem differential_tower [Algebra R S] [IsScalarTower k R S] (ω : KaehlerDifferential k R) :
    differential (IsScalarTower.toAlgHom k R S) ω = KaehlerDifferential.map k k R S ω := by
  have hω : ω ∈ Submodule.span R (Set.range (KaehlerDifferential.D k R)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem _ h => obtain ⟨r, rfl⟩ := h; rw [differential_D, KaehlerDifferential.map_D] <;> rfl
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx =>
    rw [map_smulₛₗ, map_smul, hx]
    change algebraMap R S c • KaehlerDifferential.map k k R S x =
      c • KaehlerDifferential.map k k R S x
    exact IsScalarTower.algebraMap_smul (R := R) (A := S) c _

abbrev Forms (k R : Type) [CommRing k] [CommRing R] [Algebra k R] (n : ℕ) :=
  ⋀[R]^n (KaehlerDifferential k R)

variable {T : Type} [CommRing T] [Algebra k T]

theorem differential_comp (σ : S →ₐ[k] T) (ω : KaehlerDifferential k R) :
    differential (σ.comp π) ω = differential σ (differential π ω) := by
  have hω : ω ∈ Submodule.span R (Set.range (KaehlerDifferential.D k R)) := by
    rw [KaehlerDifferential.span_range_derivation]; trivial
  induction hω using Submodule.span_induction with
  | mem _ h => obtain ⟨r, rfl⟩ := h; simp only [differential_D, AlgHom.comp_apply]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul c x _ hx => simp only [map_smulₛₗ, hx] <;> rfl

theorem restrict_comp (σ : S →ₐ[k] T) (n : ℕ) (ω : Forms k R n) :
    exteriorMap (σ.comp π).toRingHom (differential (σ.comp π)) n ω =
      exteriorMap σ.toRingHom (differential σ) n (exteriorMap π.toRingHom (differential π) n ω) :=
  CycleQ2GeometricExteriorSheaf.exteriorMap_composition _ _ _ _ _ _ (fun _ => rfl) (differential_comp π σ) n ω


/-- Wedge of the exact differentials of a list of functions. -/
def exactWedge {A : Type} [CommRing A] [Algebra k A] (n : ℕ) (t : Fin n → A) : Forms k A n :=
  exteriorPower.ιMulti A n (fun j => KaehlerDifferential.D k A (t j))

theorem pull_exactWedge (n : ℕ) (t : Fin n → R) :
    exteriorMap π.toRingHom (differential π) n (exactWedge (k := k) n t) =
      exactWedge (k := k) n (π ∘ t) := by
  rw [exactWedge,exteriorMap_wedge]
  unfold exactWedge
  simp only [differential_D,Function.comp_apply]

section Generation
variable {ι P : Type} [LinearOrder ι] [Fintype ι] [AddCommGroup P]
theorem exact_generators (b : Module.Basis ι R (KaehlerDifferential k R))
    (z : ι → R) (hb : ∀ i, b i = KaehlerDifferential.D k R (z i))
    (n : ℕ) (u v : Forms k R n →+ P)
    (h : ∀ (a : R) (t : Fin n → R), u (a • exactWedge (k := k) n t) = v (a • exactWedge (k := k) n t))
    (ω : Forms k R n) : u ω = v ω := by
  classical
  let B := b.exteriorPower n
  rw [← B.sum_repr ω, map_sum, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  have he : B i = exactWedge (k := k) n (fun j => z (Set.powersetCard.ofFinEmbEquiv.symm i j)) := by
    change b.exteriorPower n i = _
    rw [exteriorPower.basis_apply]
    simp only [exteriorPower.ιMulti_family, exactWedge, Function.comp_def, hb]
  rw [he]
  apply h
end Generation

/-- Pullback of exterior differentiation in every degree, using the
defining rule d(a df₁∧⋯∧dfₙ)=da∧df₁∧⋯∧dfₙ. -/
theorem exteriorD_natural {ι : Type} [LinearOrder ι] [Fintype ι]
    (b : Module.Basis ι R (KaehlerDifferential k R)) (z : ι → R)
    (hb : ∀ i, b i = KaehlerDifferential.D k R (z i)) (n : ℕ)
    (dr : Forms k R n →+ Forms k R (n+1)) (ds : Forms k S n →+ Forms k S (n+1))
    (hr : ∀ (a : R) (t : Fin n → R), dr (a • exactWedge (k := k) n t) = exactWedge (k := k) (n+1) (Fin.cons a t))
    (hs : ∀ (a : S) (t : Fin n → S), ds (a • exactWedge (k := k) n t) = exactWedge (k := k) (n+1) (Fin.cons a t))
    (ω : Forms k R n) :
    ds (exteriorMap π.toRingHom (differential π) n ω) =
      exteriorMap π.toRingHom (differential π) (n+1) (dr ω) := by
  refine exact_generators b z hb n
    (ds.comp (exteriorMap π.toRingHom (differential π) n).toAddMonoidHom)
    ((exteriorMap π.toRingHom (differential π) (n+1)).toAddMonoidHom.comp dr) ?_ ω
  intro a t
  change ds (exteriorMap π.toRingHom (differential π) n (a • exactWedge (k := k) n t)) = _
  rw [map_smulₛₗ, pull_exactWedge, hs]
  change _ = exteriorMap π.toRingHom (differential π) (n+1) (dr (a • exactWedge (k := k) n t))
  rw [hr,pull_exactWedge]
  apply congrArg (exactWedge (k := k) (n+1))
  funext i
  refine Fin.cases ?_ (fun j => ?_) i <;> rfl

end CycleQ2LogarithmicPullback
end

#print axioms CycleQ2LogarithmicPullback.exteriorD_natural
