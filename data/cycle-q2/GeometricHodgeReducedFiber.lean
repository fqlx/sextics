import Proposal.GeometricHodgeProjectiveShear
import Proposal.GeometricLiteralAmbientSurface

/-!
# Special fibre of the weighted coordinate changes

Reduction modulo ε induces the closed immersion of the original full-family
weighted projective hypersurface into each first-order thickening. The
isomorphisms induced by coordinate velocities commute with that immersion.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeReducedFiber

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2GeometricSurfaceFirstOrder CycleQ2HodgeInfinitesimalQuotient
open CycleQ2HodgeGradedShear CycleQ2HodgeProjectiveShear CycleQ2GeometricIncidenceProj
open CycleQ2GenericSexticGradient (CoeffRing)

variable {K : Type} [CommRing K] {χ : ZMod 3}

def reduce : JD K →+* P K := MvPolynomial.map (TrivSqZeroExt.fstHom K K K).toRingHom

@[simp] theorem reduce_lift (p : P K) : reduce (liftPoly p) = p := by
  ext d
  simp [reduce, liftPoly, coeff_map]

@[simp] theorem reduce_eps : reduce (eps : JD K) = 0 := by simp [reduce, eps]

theorem reduce_subst (v : Velocities K χ) (p : JD K) : reduce (subst v p) = reduce p := by
  induction p using MvPolynomial.induction_on with
  | C c => simp [subst]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p i hp => simp [map_mul, hp]

theorem reduce_equation (f a : P K) : reduce (equation f a) = f := by simp [equation]

def reduction (φ : CoeffRing →+* K) (a : Directions K χ) :
    cone (deformedSextic φ a) →+* CycleQ2GeometricHodgeThreefold.cone φ :=
  Ideal.quotientMap _ reduce (by
    apply Ideal.span_le.mpr
    rintro p (rfl : p = _)
    change reduce (equation (FiberPolynomial φ) a.val) ∈ Ideal.span {FiberPolynomial φ}
    rw [reduce_equation]
    exact Ideal.mem_span_singleton_self _)

def reductionGraded (φ : CoeffRing →+* K) (a : Directions K χ) :
    grading (deformedSextic φ a) →+*ᵍ CycleQ2GeometricHodgeThreefold.grade φ where
  toRingHom := reduction φ a
  map_mem := by
    rintro n _ ⟨p,hp,rfl⟩
    refine ⟨reduce p, ?_, rfl⟩
    change (reduce p).IsWeightedHomogeneous geometricWeight n
    intro d hd
    apply (show p.IsWeightedHomogeneous geometricWeight n from hp)
    intro h
    exact hd (by simp [reduce, coeff_map, h])

theorem reduction_surjective_grade (φ : CoeffRing →+* K) (a : Directions K χ) (n : ℕ)
    (x : CycleQ2GeometricHodgeThreefold.cone φ) (hx : x ∈ CycleQ2GeometricHodgeThreefold.grade φ n) :
    ∃ y ∈ grading (deformedSextic φ a) n, reductionGraded φ a y = x := by
  obtain ⟨p,hp,rfl⟩ := hx
  refine ⟨Ideal.Quotient.mk _ (liftPoly p), ⟨liftPoly p, lift_homogeneous hp, rfl⟩, ?_⟩
  exact congrArg (CycleQ2GeometricHodgeThreefold.quotient φ) (reduce_lift p)

theorem irrelevant_le (φ : CoeffRing →+* K) (a : Directions K χ) :
    HomogeneousIdeal.irrelevant (CycleQ2GeometricHodgeThreefold.grade φ) ≤
      (HomogeneousIdeal.irrelevant (grading (deformedSextic φ a))).map (reductionGraded φ a) := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le _).mpr
  intro n hn x hx
  obtain ⟨y,hy,rfl⟩ := reduction_surjective_grade φ a n x hx
  exact Ideal.mem_map_of_mem (reductionGraded φ a)
    (HomogeneousIdeal.mem_irrelevant_of_mem (grading (deformedSextic φ a)) hn hy)

def specialFiber (φ : CoeffRing →+* K) (a : Directions K χ) :
    CycleQ2GeometricHodgeThreefold.threefold φ ⟶ thickening (deformedSextic φ a) :=
  Proj.map (reductionGraded φ a) (irrelevant_le φ a)

instance (φ : CoeffRing →+* K) (a : Directions K χ) : IsClosedImmersion (specialFiber φ a) :=
  CycleQ2LiteralAmbientSurface.projectiveMap_closedImmersion _ _ (reductionGraded φ a)
    (irrelevant_le φ a) (reduction_surjective_grade φ a)

theorem projectiveEquiv_reduction (φ : CoeffRing →+* K) (a b : Directions K χ)
    (v : Velocities K χ) (h : subst v (deformedSextic φ a).val = (deformedSextic φ b).val) :
    specialFiber φ a ≫ (projectiveEquiv v h).hom = specialFiber φ b := by
  change Proj.map _ _ ≫ Proj.map (backward v h) _ = Proj.map _ _
  rw [← Proj.map_comp]
  congr 1
  apply GradedRingHom.ext
  intro z
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective z
  exact congrArg (CycleQ2GeometricHodgeThreefold.quotient φ) (reduce_subst (-v) p)

/-- The structure map exhibits the base of each deformed equation as the dual scalars. -/
def toDual (f : Sextic K) : thickening f ⟶ Spec (CommRingCat.of (Dual K)) :=
  Proj.toSpecZero (grading f) ≫ Spec.map (CommRingCat.ofHom (algebraMap (Dual K) (grading f 0)))

theorem projectiveEquiv_overDual {f g : Sextic K} (v : Velocities K χ)
    (h : subst v f.val = g.val) : (projectiveEquiv v h).hom ≫ toDual g = toDual f := by
  change Proj.map (backward v h) _ ≫ _ = _
  rw [toDual, ← Category.assoc, CycleQ2IncidenceFamilyContainment.projectiveMap_toSpecZero,
    Category.assoc, ← Spec.map_comp]
  unfold toDual
  congr 1
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro c
  apply Subtype.ext
  exact (coneEquiv v h).symm.commutes c

end CycleQ2HodgeReducedFiber
end

#print axioms CycleQ2HodgeReducedFiber.projectiveEquiv_reduction
#print axioms CycleQ2HodgeReducedFiber.projectiveEquiv_overDual
