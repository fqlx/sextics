import Proposal.GeometricLiteralOrbitNegativeSections
import Proposal.GeometricLiteralOrbitAction

/-!
# The three components of the orbit divisor on a common subopen

Reduction of the numerator modulo the three translated curve ideals gives
an algebra isomorphism from its residue modulo the pivot equation. The
component maps commute with restriction and a change of local frame.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingPoleComponents

open CategoryTheory AlgebraicGeometry MvPolynomial CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedSectionDivisorTransitions CycleQ2SeedSectionSheafGlobal
  CycleQ2LiteralMovingDivisorOrbitFrames CycleQ2LiteralOrbitNegativeSections
  CycleQ2LinkageComponentDecomposition CycleQ2LinkageComponentAlgebra
  CycleQ2SeedTrace CycleQ2NormalConnecting CycleQ2CartierSurfaceGrading
  CycleQ2SeedCyclicAction CycleQ2LiteralOrbitAction

variable {W V : Surface.Opens}

abbrev pivotIdeal (f : FrameData W) : Ideal Γ(Surface,W) := Ideal.span {pivotEquation f}

abbrev componentIdeal (f : FrameData W) (a : Fin 3) : Ideal Γ(Surface,W) :=
  translateIdeal f.chart W f.within (rootValues complexRoot a)

theorem component_coprime (f : FrameData W) : Pairwise (fun a b => IsCoprime (componentIdeal f a) (componentIdeal f b)) := by
  intro a b hab
  apply Ideal.isCoprime_iff_sup_eq.mpr
  apply translateIdeal_sup_top _ _ _ (rootValues_cube complexRoot complexRoot_quadratic a)
    (rootValues_cube complexRoot complexRoot_quadratic b)
  exact sub_ne_zero.mp (complexRoot_units a b hab).1.ne_zero

theorem pivotIdeal_eq_iInf (f : FrameData W) : pivotIdeal f = ⨅ a, componentIdeal f a := by
  have h := Ideal.prod_eq_iInf_of_pairwise_isCoprime (s := Finset.univ) (J := componentIdeal f)
    (fun _ _ _ _ h => component_coprime f h)
  simp only [Finset.mem_univ, iInf_pos, Fin.prod_univ_three] at h
  exact (pivotEquation_span_product f).trans h

/-- Reduction on each component is linear over the original section ring. -/
def components (f : FrameData W) : (Γ(Surface,W) ⧸ pivotIdeal f) ≃ₐ[Γ(Surface,W)]
    (∀ a, Γ(Surface,W) ⧸ componentIdeal f a) :=
  AlgEquiv.ofRingEquiv (f := (Ideal.quotEquivOfEq (pivotIdeal_eq_iInf f)).trans
    (Ideal.quotientInfRingEquivPiQuotient (componentIdeal f) (component_coprime f))) (fun _ => rfl)

@[simp] theorem components_mk (f : FrameData W) (r : Γ(Surface,W)) (a : Fin 3) :
    components f (Ideal.Quotient.mk _ r) a = Ideal.Quotient.mk (componentIdeal f a) r := rfl

private theorem componentIdeal_change (f g : FrameData W) (a : Fin 3) :
    componentIdeal f a = componentIdeal g a := by
  let z := rootValues complexRoot a
  have hz := rootValues_cube complexRoot complexRoot_quadratic a
  rw [componentIdeal, componentIdeal, translateIdeal_eq_pair _ _ _ _ hz, translateIdeal_eq_pair _ _ _ _ hz]
  let u := transitionUnit f.chart g.chart W f.within g.within ^ 2
  rw [polynomialSection_change f.chart g.chart W f.within g.within 2 _
    (polynomialAction_weighted z (originalF1_homogeneous 57)),
    polynomialSection_change f.chart g.chart W f.within g.within 2 _ (polynomialAction_weighted z originalF2_homogeneous)]
  symm
  change Ideal.span {(u : Γ(Surface,W)) * _, (u : Γ(Surface,W)) * _} = _
  rw [Ideal.span_insert, Ideal.span_singleton_mul_left_unit u.isUnit,
    Ideal.span_singleton_mul_left_unit u.isUnit, ← Ideal.span_insert]

/-- The restriction sends each component ideal onto its extended ideal in
any chosen frame on the smaller open. -/
theorem componentIdeal_map (f : FrameData W) (g : FrameData V) (h : V ≤ W) (a : Fin 3) :
    (componentIdeal f a).map (targetRes h) = componentIdeal g a :=
  (translateIdeal_restrict f.chart f.within _ h).trans (componentIdeal_change (f.restrict h) g a)

theorem pivotIdeal_map (f : FrameData W) (g : FrameData V) (h : V ≤ W) :
    (pivotIdeal f).map (targetRes h) = pivotIdeal g := by
  have eqn := orbitTransition_generator (f.restrict h) g
  change pivotEquation g = (orbitTransition (f.restrict h) g : Γ(Surface,V)) * pivotEquation (f.restrict h) at eqn
  rw [pivotIdeal, Ideal.map_span, Set.image_singleton, pivotEquation_restrict, pivotIdeal, eqn,
    Ideal.span_singleton_mul_left_unit (orbitTransition (f.restrict h) g).isUnit]

def pivotRestrict (f : FrameData W) (g : FrameData V) (h : V ≤ W) :
    Γ(Surface,W) ⧸ pivotIdeal f →+* Γ(Surface,V) ⧸ pivotIdeal g :=
  Ideal.quotientMap _ (targetRes h) (Ideal.map_le_iff_le_comap.mp (pivotIdeal_map f g h).le)

def componentRestrict (f : FrameData W) (g : FrameData V) (h : V ≤ W) (a : Fin 3) :
    Γ(Surface,W) ⧸ componentIdeal f a →+* Γ(Surface,V) ⧸ componentIdeal g a :=
  Ideal.quotientMap _ (targetRes h) (Ideal.map_le_iff_le_comap.mp (componentIdeal_map f g h a).le)

theorem components_restrict (f : FrameData W) (g : FrameData V) (h : V ≤ W)
    (x : Γ(Surface,W) ⧸ pivotIdeal f) (a : Fin 3) :
    components g (pivotRestrict f g h x) a = componentRestrict f g h a (components f x a) := by
  obtain ⟨r,rfl⟩ := Ideal.Quotient.mk_surjective x
  rfl

/-- Changing the numerator by a frame unit multiplies each residue by the
same restricted unit in its own quotient ring. -/
theorem components_restrict_unit (f : FrameData W) (g : FrameData V) (h : V ≤ W)
    (u : Γ(Surface,V)ˣ) (x : Γ(Surface,W) ⧸ pivotIdeal f) (a : Fin 3) :
    components g ((u : Γ(Surface,V)) • pivotRestrict f g h x) a =
      (u : Γ(Surface,V)) • componentRestrict f g h a (components f x a) := by
  rw [map_smul]
  exact congrArg (fun y => (u : Γ(Surface,V)) • y) (components_restrict f g h x a)

end CycleQ2LiteralMovingPoleComponents

end

#print axioms CycleQ2LiteralMovingPoleComponents.components
#print axioms CycleQ2LiteralMovingPoleComponents.components_restrict_unit
