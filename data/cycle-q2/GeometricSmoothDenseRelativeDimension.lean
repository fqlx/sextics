import Proposal.GeometricSmoothImageDimension
import Proposal.GeometricDenseOpenAffineSections
import Mathlib.AlgebraicGeometry.Fiber
import Mathlib.AlgebraicGeometry.Noetherian

/-!
# Relative dimension on a dense open of a smooth morphism

A nonempty fiber detects the relative dimension of a smooth chart. Every
chart of a smooth morphism meets a dense open, so a single relative
dimension on that open determines the relative dimension everywhere.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2SmoothDenseRelativeDimension

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace CycleQ2SweptSupport

private theorem dimension_eq_field {K : Type} [Field K] {X : Scheme.{0}} [NoetherianSpace X]
    (x : X) (f : X ⟶ Spec (CommRingCat.of K)) (a b : ℕ)
    [SmoothOfRelativeDimension a f] [SmoothOfRelativeDimension b f] : a = b := by
  have hd : DenseRange (𝟙 X : X ⟶ X) := by
    change DenseRange (id : X → X)
    exact denseRange_id
  have aux (m n : ℕ) [SmoothOfRelativeDimension m f] [SmoothOfRelativeDimension n f] :
      ¬ m < n := fun h ↦ closure_range_ne_univ m n h f f x (𝟙 X) (Category.id_comp _)
        hd.closure_eq
  exact Nat.le_antisymm (Nat.le_of_not_gt (aux b a)) (Nat.le_of_not_gt (aux a b))

private theorem fiber_dimension {X B : Scheme.{0}} (f : X ⟶ B) (s : B) (d : ℕ)
    [SmoothOfRelativeDimension d f] : SmoothOfRelativeDimension d (f.fiberToSpecResidueField s) := by
  let _ : MorphismProperty.IsStableUnderBaseChange (@SmoothOfRelativeDimension.{0} d) :=
    smoothOfRelativeDimension_isStableUnderBaseChange d
  exact MorphismProperty.pullback_snd _ _ inferInstance

/-- The dimension of a nonempty smooth family is unique. -/
theorem dimension_eq {X B : Scheme.{0}} [NoetherianSpace X] (x : X) (f : X ⟶ B) (a b : ℕ)
    [SmoothOfRelativeDimension a f] [SmoothOfRelativeDimension b f] : a = b := by
  let s := f x
  let q := f.fiberToSpecResidueField s
  have : SmoothOfRelativeDimension a q := fiber_dimension f s a
  have : SmoothOfRelativeDimension b q := fiber_dimension f s b
  have : Smooth q := SmoothOfRelativeDimension.smooth a q
  have : IsLocallyNoetherian (f.fiber s) := LocallyOfFiniteType.isLocallyNoetherian q
  have : IsNoetherian (f.fiber s) := {}
  exact dimension_eq_field (K := B.residueField s) (X := f.fiber s) (f.asFiber x) q a b

/-- A smooth morphism has relative dimension d everywhere if it has relative
dimension d on a dense open with Noetherian underlying space. -/
theorem relativeDimension_of_dense_open {X Y B : Scheme.{0}} [NoetherianSpace Y]
    (j : Y ⟶ X) [IsOpenImmersion j] [IsDominant j] (f : X ⟶ B) (d : ℕ)
    [Smooth f] [SmoothOfRelativeDimension d (j ≫ f)] : SmoothOfRelativeDimension d f := by
  constructor
  intro x
  obtain ⟨O, hO, V, hV, hx, hle, hs⟩ := Smooth.exists_isStandardSmooth (f := f) x
  let A := Γ(X, V)
  let l := (f.appLE O V hle).hom
  let : Algebra Γ(B, O) A := l.toAlgebra
  have hs' : Algebra.IsStandardSmooth Γ(B, O) A := hs
  obtain ⟨ι, σ, hσ, hι, ⟨P⟩⟩ := hs'.out
  let n := P.dimension
  have hn : l.IsStandardSmoothOfRelativeDimension n := P.isStandardSmoothOfRelativeDimension rfl
  have : SmoothOfRelativeDimension n (Spec.map (f.appLE O V hle)) := by
    apply (HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension n)).mpr
    exact RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ hn
  have : SmoothOfRelativeDimension n (hV.fromSpec ≫ f) := by
    rw [← IsAffineOpen.SpecMap_appLE_fromSpec f hO hV hle]
    simpa only [Nat.add_zero] using
      smoothOfRelativeDimension_comp n 0 (Spec.map (f.appLE O V hle)) hO.fromSpec
  let W := j ⁻¹ᵁ V
  let t : W.toScheme ⟶ Spec A := CycleQ2DenseOpenAffineSections.chart j hV
  let p := W.ι ≫ j ≫ f
  have htp : t ≫ hV.fromSpec ≫ f = p := by
    change ((j ∣_ V) ≫ hV.isoSpec.hom) ≫ hV.fromSpec ≫ f = _
    simp only [IsAffineOpen.fromSpec, Iso.hom_inv_id_assoc, Category.assoc,
      morphismRestrict_ι_assoc, p, W]
  have : SmoothOfRelativeDimension n p := by
    rw [← htp]
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 n t (hV.fromSpec ≫ f)
  have : SmoothOfRelativeDimension d p := by
    simpa only [Nat.zero_add] using smoothOfRelativeDimension_comp 0 d W.ι (j ≫ f)
  have : NoetherianSpace W.toScheme := NoetherianSpace.set (W : Set Y)
  obtain ⟨y, hy⟩ := j.denseRange.exists_mem_open V.isOpen ⟨x, hx⟩
  have hnd := dimension_eq (X := W.toScheme) ⟨y, hy⟩ p n d
  exact ⟨O, hO, V, hV, hx, hle, hnd ▸ hn⟩

/-- After restriction to any base open over which the model is smooth,
the dense original family still determines its relative dimension. -/
theorem relativeDimension_on_restriction {X Y B : Scheme.{0}} [NoetherianSpace Y]
    (j : Y ⟶ X) [IsOpenImmersion j] [IsDominant j] (f : X ⟶ B) (D : B.Opens) (d : ℕ)
    [Smooth (f ∣_ D)] [SmoothOfRelativeDimension d (j ≫ f)] :
    SmoothOfRelativeDimension d (f ∣_ D) := by
  let i := j ∣_ (f ⁻¹ᵁ D)
  have : NoetherianSpace (j ⁻¹ᵁ (f ⁻¹ᵁ D)).toScheme :=
    NoetherianSpace.set (j ⁻¹ᵁ (f ⁻¹ᵁ D) : Set Y)
  have : IsDominant i := ⟨denseRange_restrict j j.denseRange _⟩
  have : SmoothOfRelativeDimension d (i ≫ (f ∣_ D)) := by
    change SmoothOfRelativeDimension d ((j ∣_ (f ⁻¹ᵁ D)) ≫ (f ∣_ D))
    rw [← morphismRestrict_comp]
    exact IsZariskiLocalAtTarget.restrict (P := @SmoothOfRelativeDimension d) inferInstance D
  exact relativeDimension_of_dense_open i (f ∣_ D) d

end CycleQ2SmoothDenseRelativeDimension

#print axioms CycleQ2SmoothDenseRelativeDimension.dimension_eq
#print axioms CycleQ2SmoothDenseRelativeDimension.relativeDimension_of_dense_open

#print axioms CycleQ2SmoothDenseRelativeDimension.relativeDimension_on_restriction
