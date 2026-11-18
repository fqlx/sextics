import Proposal.GeometricHodgeGradedShear
import Proposal.GeometricHodgeThreefold

/-!
# The projective isomorphism from an infinitesimal coordinate change

The weighted graded rings of the equations F − εa and F − εb are
isomorphic for directions differing by a weighted coordinate velocity.
Projectivizing gives an isomorphism of the corresponding threefold
deformations. The coefficient ring consists of the actual dual numbers.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeProjectiveShear

open CategoryTheory AlgebraicGeometry MvPolynomial
open CycleQ2GeometricIncidenceProj CycleQ2GeometricSurfaceFirstOrder CycleQ2HodgeGradedShear
open CycleQ2GeometricProjectiveCurve.HomogeneousQuotient
open CycleQ2HodgeInfinitesimalQuotient
open CycleQ2GenericSexticGradient (CoeffRing)
attribute [local instance] MvPolynomial.weightedGradedAlgebra

variable {K : Type} [CommRing K] {χ : ZMod 3}

abbrev Sextic (K : Type) [CommRing K] := weightedHomogeneousSubmodule (Dual K) geometricWeight 6

abbrev ideal (f : Sextic K) := Ideal.span ({f.val} : Set (JD K))
abbrev cone (f : Sextic K) := JD K ⧸ ideal f
abbrev grading (f : Sextic K) (n : ℕ) := grade (PolynomialGrade (Dual K)) (ideal f) n

instance (f : Sextic K) : GradedRing (grading f) :=
  gradedRing _ _ (Ideal.homogeneous_span _ _ (by
    rintro p (rfl : p = f.val)
    exact ⟨6, f.property⟩))

/-- The genuine weighted projective equation over the dual coefficient ring. -/
abbrev thickening (f : Sextic K) := Proj (grading f)

variable {f g : Sextic K}

def coneEquiv (v : Velocities K χ) (h : subst v f.val = g.val) : cone f ≃ₐ[Dual K] cone g :=
  Ideal.quotientEquivAlg _ _ (coordinateEquiv v) (by
    rw [ideal, ideal, Ideal.map_span, Set.image_singleton]
    exact congrArg (fun p : JD K => Ideal.span {p}) h.symm)

def forward (v : Velocities K χ) (h : subst v f.val = g.val) : grading f →+*ᵍ grading g where
  toRingHom := (coneEquiv v h).toRingHom
  map_mem := by
    rintro n _ ⟨p,hp,rfl⟩
    exact ⟨subst v p, subst_homogeneous v hp, rfl⟩

def backward (v : Velocities K χ) (h : subst v f.val = g.val) : grading g →+*ᵍ grading f where
  toRingHom := (coneEquiv v h).symm.toRingHom
  map_mem := by
    rintro n _ ⟨p,hp,rfl⟩
    exact ⟨subst (-v) p, subst_homogeneous (-v) hp, rfl⟩

private theorem irrelevant_le {A B : Type} [CommRing A] [CommRing B]
    {S T : Type} [SetLike S A] [SetLike T B]
    [AddSubmonoidClass S A] [AddSubmonoidClass T B]
    {𝒜 : ℕ → S} {ℬ : ℕ → T} [GradedRing 𝒜] [GradedRing ℬ]
    (F : 𝒜 →+*ᵍ ℬ) (G : ℬ →+*ᵍ 𝒜) (hFG : ∀ x, F (G x) = x) :
    HomogeneousIdeal.irrelevant ℬ ≤ (HomogeneousIdeal.irrelevant 𝒜).map F := by
  apply (HomogeneousIdeal.toIdeal_irrelevant_le ℬ).mpr
  intro n hn x hx
  have hy := HomogeneousIdeal.mem_irrelevant_of_mem 𝒜 hn (G.map_mem hx)
  exact hFG x ▸ Ideal.mem_map_of_mem F hy

def projectiveEquiv (v : Velocities K χ) (h : subst v f.val = g.val) :
    thickening f ≅ thickening g := by
  let F := forward v h
  let G := backward v h
  have hFG (x : cone g) : F (G x) = x := (coneEquiv v h).apply_symm_apply x
  have hGF (x : cone f) : G (F x) = x := (coneEquiv v h).symm_apply_apply x
  refine ⟨Proj.map G (irrelevant_le G F hGF), Proj.map F (irrelevant_le F G hFG), ?_, ?_⟩
  · rw [← Proj.map_comp]
    simp only [show G.comp F = GradedRingHom.id (grading f) from GradedRingHom.ext hGF,
      Proj.map_id]
  · rw [← Proj.map_comp]
    simp only [show F.comp G = GradedRingHom.id (grading g) from GradedRingHom.ext hFG,
      Proj.map_id]

def deformedSextic (φ : CoeffRing →+* K) (a : Directions K χ) : Sextic K :=
  ⟨equation (FiberPolynomial φ) a.val,
    (lift_homogeneous (CycleQ2GeometricHodgeThreefold.equation_homogeneous φ)).sub
      ((lift_homogeneous (homogeneous_of_character a.property)).C_mul _)⟩

theorem projectiveEquiv_of_class_eq (φ : CoeffRing →+* K) (a b : Directions K χ)
    (h : directionClass φ χ a = directionClass φ χ b) :
    Nonempty (thickening (deformedSextic φ a) ≅ thickening (deformedSextic φ b)) := by
  rw [← sub_eq_zero, ← map_sub, ← LinearMap.mem_ker, ker_directionClass] at h
  obtain ⟨v,hv⟩ := h
  have hD : velocityDerivation v (FiberPolynomial φ) = a.val - b.val := congrArg Subtype.val hv
  refine ⟨projectiveEquiv v ?_⟩
  change subst v (equation (FiberPolynomial φ) a.val) = equation (FiberPolynomial φ) b.val
  rw [subst_equation, hD, sub_sub_cancel]

end CycleQ2HodgeProjectiveShear
end

#print axioms CycleQ2HodgeProjectiveShear.projectiveEquiv_of_class_eq
