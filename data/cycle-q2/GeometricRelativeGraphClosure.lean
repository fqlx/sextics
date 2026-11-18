import Proposal.GeometricImmersionImageClosure

/-!
# Closing a family of embedded correspondences in a relative product

A closed correspondence over an open time scheme embeds in the product with
a compactified time scheme. Its scheme-theoretic closure recovers the
original family by base change to the time open, with both projections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false

noncomputable section
namespace CycleQ2RelativeGraphClosure

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u
variable {B U P T X : Scheme.{u}} (u : U ⟶ B) (p : P ⟶ B) (a : T ⟶ B)
  (j : U ⟶ P) (hj : j ≫ p = u)

/-- The inclusion of the product over the time open into the compactifying product. -/
def productMap : pullback u a ⟶ pullback p a :=
  pullback.lift (pullback.fst u a ≫ j) (pullback.snd u a)
    (by rw [Category.assoc, hj, pullback.condition])

@[reassoc (attr := simp)]
theorem productMap_fst :
    productMap u p a j hj ≫ pullback.fst p a = pullback.fst u a ≫ j :=
  pullback.lift_fst _ _ _

@[reassoc (attr := simp)]
theorem productMap_snd :
    productMap u p a j hj ≫ pullback.snd p a = pullback.snd u a :=
  pullback.lift_snd _ _ _

theorem product_square :
    IsPullback (pullback.fst u a) (productMap u p a j hj) j (pullback.fst p a) := by
  apply IsPullback.of_bot _ (productMap_fst u p a j hj).symm (IsPullback.of_hasPullback p a)
  simpa only [productMap_snd, hj] using IsPullback.of_hasPullback u a

instance [IsOpenImmersion j] : IsOpenImmersion (productMap u p a j hj) :=
  MorphismProperty.of_isPullback (product_square u p a j hj) inferInstance

instance [QuasiCompact j] : QuasiCompact (productMap u p a j hj) :=
  MorphismProperty.of_isPullback (product_square u p a j hj) inferInstance

variable (g : X ⟶ pullback u a)

abbrev graph := g ≫ productMap u p a j hj

abbrev Closure := (graph u p a j hj g).image
abbrev toClosure := (graph u p a j hj g).toImage
abbrev embedding := (graph u p a j hj g).imageι

def timeProjection : Closure u p a j hj g ⟶ P :=
  embedding u p a j hj g ≫ pullback.fst p a

def targetProjection : Closure u p a j hj g ⟶ T :=
  embedding u p a j hj g ≫ pullback.snd p a

@[reassoc (attr := simp)]
theorem toClosure_timeProjection :
    toClosure u p a j hj g ≫ timeProjection u p a j hj g = g ≫ pullback.fst u a ≫ j := by
  rw [timeProjection, ← Category.assoc, Scheme.Hom.toImage_imageι]
  simp only [graph, Category.assoc, productMap_fst]

@[reassoc (attr := simp)]
theorem toClosure_targetProjection :
    toClosure u p a j hj g ≫ targetProjection u p a j hj g = g ≫ pullback.snd u a := by
  rw [targetProjection, ← Category.assoc, Scheme.Hom.toImage_imageι]
  simp only [graph, Category.assoc, productMap_snd]

instance [IsProper p] : IsProper (targetProjection u p a j hj g) := by
  unfold targetProjection
  infer_instance

instance [IsProper a] : IsProper (timeProjection u p a j hj g) := by
  unfold timeProjection
  infer_instance

variable [IsClosedImmersion g] [IsOpenImmersion j] [QuasiCompact j]

theorem recovery :
    IsPullback (g ≫ pullback.fst u a) (toClosure u p a j hj g) j (timeProjection u p a j hj g) :=
  (CycleQ2ImmersionImageClosure.closed_in_open_pullback g (productMap u p a j hj)).paste_horiz
    (product_square u p a j hj)

instance : IsOpenImmersion (toClosure u p a j hj g) :=
  MorphismProperty.of_isPullback (recovery u p a j hj g) inferInstance

instance : IsDominant (toClosure u p a j hj g) :=
  inferInstanceAs (IsDominant (g ≫ productMap u p a j hj).toImage)

end CycleQ2RelativeGraphClosure

#print axioms CycleQ2RelativeGraphClosure.recovery
