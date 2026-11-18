import Proposal.GeometricLiteralTimeCurveBoundary
import Proposal.GeometricFiniteEtaleParameterPoint
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Complex points at the boundary of the proper time base

At a closed point of a finite-type complex scheme, the structure morphism
makes the residue field a finite extension of the algebraically closed base.
Its inverse provides a complex-valued point over the base with exactly the
specified image. This applies to every boundary point of the time-curve
completion and of its finite normalization.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralTimeCurveBoundaryPoints

open AlgebraicGeometry CategoryTheory
open CycleQ2FiniteEtaleParameterPoint

variable {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of ℂ)) [LocallyOfFiniteType f]

/-- The original coefficient map identifies the complex field with the residue
field of every closed point. -/
theorem coefficient_bijective (x : X) (hx : IsClosed {x}) :
    Function.Bijective (pointFieldMap f x).hom :=
  IsAlgClosed.ringHom_bijective_of_isIntegral _ (pointFieldMap_finite f x hx).to_isIntegral

/-- The algebra equivalence uses the structure algebra from the original morphism. -/
def residueEquiv (x : X) (hx : IsClosed {x}) :
    letI := (pointFieldMap f x).hom.toAlgebra
    ℂ ≃ₐ[ℂ] X.residueField x := by
  letI := (pointFieldMap f x).hom.toAlgebra
  exact AlgEquiv.ofBijective (Algebra.ofId ℂ (X.residueField x)) (coefficient_bijective f x hx)

/-- A closed point has a complex-valued representative that is a section of
the given structure morphism. -/
theorem exists_section (x : X) (hx : IsClosed {x}) :
    ∃ b : Spec (CommRingCat.of ℂ) ⟶ X, b ≫ f = 𝟙 _ ∧ ∀ z, b z = x := by
  let e : CommRingCat.of ℂ ≅ X.residueField x :=
    (RingEquiv.ofBijective (pointFieldMap f x).hom (coefficient_bijective f x hx)).toCommRingCatIso
  have he : e.hom = pointFieldMap f x := rfl
  refine ⟨Spec.map e.inv ≫ X.fromSpecResidueField x, ?_, fun z => ?_⟩
  · rw [Category.assoc, ← pointFieldMap_spec, ← he, ← Spec.map_comp, e.hom_inv_id, Spec.map_id]
  · simp only [Scheme.Hom.comp_apply, Scheme.fromSpecResidueField_apply]

/-- The residue extension at a complex-rational source point is trivial for
every morphism over the complex base. -/
theorem residueFieldMap_bijective {Y : Scheme.{0}} (g : X ⟶ Y)
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) (hg : g ≫ p = f) (x : X) (hx : IsClosed {x}) :
    Function.Bijective (g.residueFieldMap x).hom := by
  have hfac : pointFieldMap p (g x) ≫ g.residueFieldMap x = pointFieldMap f x := by
    apply Spec.map_injective
    simp only [Spec.map_comp, pointFieldMap_spec,
      Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField_assoc, hg]
  refine ⟨RingHom.injective _, ?_⟩
  intro z
  obtain ⟨c, hc⟩ := (coefficient_bijective f x hx).surjective z
  exact ⟨(pointFieldMap p (g x)).hom c,
    (congrArg (fun h : CommRingCat.of ℂ ⟶ X.residueField x => h.hom c) hfac).trans hc⟩

theorem residueFieldMap_separable {Y : Scheme.{0}} (g : X ⟶ Y)
    (p : Y ⟶ Spec (CommRingCat.of ℂ)) (hg : g ≫ p = f) (x : X) (hx : IsClosed {x}) :
    letI := (g.residueFieldMap x).hom.toAlgebra
    Algebra.IsSeparable (Y.residueField (g x)) (X.residueField x) := by
  let : Algebra (Y.residueField (g x)) (X.residueField x) := (g.residueFieldMap x).hom.toAlgebra
  constructor
  intro z
  obtain ⟨a, rfl⟩ := (residueFieldMap_bijective f g p hg x hx).surjective z
  exact isSeparable_algebraMap a

open CycleQ2LiteralIncidenceTimeCurve CycleQ2LiteralTimeCurveCompletion
  CycleQ2LiteralTimeCurveNormalization CycleQ2LiteralTimeCurveBoundary

/-- Every point added by the projective completion is complex-rational over
the original structure map. -/
theorem completion_point (U : Curve.Opens) (x : Completion U)
    (hx : x ∉ Set.range (inclusion U)) :
    ∃ b : Spec (CommRingCat.of ℂ) ⟶ Completion U,
      b ≫ structureMap U = 𝟙 _ ∧ ∀ z, b z = x :=
  exists_section (structureMap U) x ((completion_boundary U).2 hx)

/-- Every point added by the normalization gives a complex-valued section
over the original complex base. -/
theorem normalization_point (U : Curve.Opens) (x : Normalization U)
    (hx : x ∉ Set.range (openInclusion U)) :
    ∃ b : Spec (CommRingCat.of ℂ) ⟶ Normalization U,
      b ≫ toComplexPoint U = 𝟙 _ ∧ ∀ z, b z = x :=
  exists_section (toComplexPoint U) x ((normalization_boundary U).2 hx)

/-- For every affine-line coordinate defined near a normalized boundary point,
the induced extension of its two actual scheme residue fields is separable. -/
theorem normalization_coordinate_separable (U : Curve.Opens) (x : Normalization U)
    (hx : x ∉ Set.range (openInclusion U)) (V : (Normalization U).Opens) (hxV : x ∈ V)
    (g : V.toScheme ⟶ Spec (CommRingCat.of (Polynomial ℂ)))
    (hg : g ≫ Spec.map (CommRingCat.ofHom (Polynomial.C : ℂ →+* Polynomial ℂ)) =
      V.ι ≫ toComplexPoint U) :
    let v : V.toScheme := ⟨x, hxV⟩
    letI := (g.residueFieldMap v).hom.toAlgebra
    Algebra.IsSeparable ((Spec (CommRingCat.of (Polynomial ℂ))).residueField (g v))
      (V.toScheme.residueField v) := by
  let v : V.toScheme := ⟨x, hxV⟩
  have hclosed : IsClosed ({x} : Set (Normalization U)) := (normalization_boundary U).2 hx
  have hv : v ∈ closedPoints V.toScheme :=
    (preimage_closedPoints_subset V.ι.isOpenEmbedding.injective V.ι.continuous)
      (show V.ι v ∈ closedPoints (Normalization U) from hclosed)
  exact residueFieldMap_separable (V.ι ≫ toComplexPoint U) g _ hg v hv

end CycleQ2LiteralTimeCurveBoundaryPoints
end

#print axioms CycleQ2LiteralTimeCurveBoundaryPoints.residueEquiv
#print axioms CycleQ2LiteralTimeCurveBoundaryPoints.completion_point
#print axioms CycleQ2LiteralTimeCurveBoundaryPoints.normalization_point

#print axioms CycleQ2LiteralTimeCurveBoundaryPoints.normalization_coordinate_separable
