import Proposal.GeometricExteriorPullComposition

/-!
# Relative differential forms over a coefficient ring

A morphism to the spectrum of a commutative ring gives compatible scalars
on every open. Sheafifying the universal modules of Kähler differentials
over those scalars yields the relative cotangent sheaf. A morphism of
schemes over the base pulls its exterior powers back by applying the
structure map to functions before differentiating.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2FieldRelativeForms

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricExteriorSheaf CycleQ2LiteralAbelJacobiQPullback

variable {K : Type} [CommRing K] {X Y Z : Scheme.{0}}

/-- The action of the coefficient ring on global functions. -/
def coefficient (p : X ⟶ Spec (CommRingCat.of K)) : K →+* Γ(X, ⊤) :=
  ((Scheme.ΓSpecIso (CommRingCat.of K)).inv ≫ p.appTop).hom

def coefficientOn (p : X ⟶ Spec (CommRingCat.of K)) (U : X.Opens) : K →+* Γ(X,U) :=
  (X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op).hom.comp (coefficient p)

def coefficientMap (p : X ⟶ Spec (CommRingCat.of K)) :
    (Functor.const _).obj (CommRingCat.of K) ⟶ X.presheaf where
  app U := CommRingCat.ofHom (coefficientOn p U.unop)
  naturality {U V} f := by
    ext a
    change X.presheaf.map (homOfLE le_top).op (coefficient p a) =
      (X.presheaf.map (homOfLE le_top).op ≫ X.presheaf.map f) (coefficient p a)
    rw [← X.presheaf.map_comp]
    congr 2

theorem coefficientOn_app (i : Y ⟶ X) (p : X ⟶ Spec (CommRingCat.of K))
    (U : X.Opens) (a : K) :
    i.app U (coefficientOn p U a) = coefficientOn (i ≫ p) (i ⁻¹ᵁ U) a :=
  congrArg (fun k => k (coefficient p a)) (i.naturality (homOfLE (show U ≤ ⊤ from le_top)).op)

variable (p : X ⟶ Spec (CommRingCat.of K))

/-- The presheaf of universal Kähler modules over the actual scalar maps. -/
abbrev differentialPresheaf : PresheafOfModules.{0} X.ringCatSheaf.obj :=
  PresheafOfModules.DifferentialsConstruction.relativeDifferentials' (coefficientMap p)

/-- The sheaf of relative one-forms for the structure map to the coefficient spectrum. -/
def differentials : X.Modules :=
  (PresheafOfModules.sheafification (𝟙 X.ringCatSheaf.obj)).obj (differentialPresheaf p)

/-- The universal sheaf-valued differential. -/
def differential : (differentials p).val.Derivation' (coefficientMap p) :=
  (PresheafOfModules.DifferentialsConstruction.derivation' (coefficientMap p)).postcomp
    ((PresheafOfModules.sheafificationAdjunction (𝟙 X.ringCatSheaf.obj)).unit.app
      (differentialPresheaf p))

/-- The universal property of the sheafification of the relative Kähler module. -/
def homDerivationEquiv (M : X.Modules) :
    (differentials p ⟶ M) ≃ M.val.Derivation' (coefficientMap p) :=
  (PresheafOfModules.sheafificationHomEquiv (𝟙 X.ringCatSheaf.obj)).trans
    { toFun := (PresheafOfModules.DifferentialsConstruction.derivation' (coefficientMap p)).postcomp
      invFun := (PresheafOfModules.DifferentialsConstruction.isUniversal' (coefficientMap p)).desc
      left_inv := fun _ =>
        (PresheafOfModules.DifferentialsConstruction.isUniversal' (coefficientMap p)).postcomp_injective
          _ _ ((PresheafOfModules.DifferentialsConstruction.isUniversal' (coefficientMap p)).fac _)
      right_inv := (PresheafOfModules.DifferentialsConstruction.isUniversal' (coefficientMap p)).fac }

theorem homDerivationEquiv_apply (M : X.Modules) (f : differentials p ⟶ M)
    (U : X.Opens) (a : Γ(X,U)) :
    (homDerivationEquiv p M f).d a = f.val.app (op U) ((differential p).d a) := rfl

/-- The relative exterior form sheaf in degree `n`. -/
def forms (n : ℕ) : X.Modules := exteriorSheaf X.sheaf (differentials p).val n

variable (i : Y ⟶ X)

private def pullDerivation :
    ((Scheme.Modules.pushforward i).obj (differentials (i ≫ p))).val.Derivation' (coefficientMap p) where
  d {U} := ((differential (i ≫ p)).d (X := op (i ⁻¹ᵁ U.unop))).comp (i.app U.unop).hom.toAddMonoidHom
  d_mul {U} a b := by
    change (differential (i ≫ p)).d (i.app U.unop (a * b)) = _
    rw [map_mul, (differential (i ≫ p)).d_mul]
    rfl
  d_map {U V} f a := by
    change (differential (i ≫ p)).d (i.app V.unop (X.presheaf.map f a)) =
      (differentials (i ≫ p)).val.map ((Opens.map i.base).map f.unop).op
        ((differential (i ≫ p)).d (i.app U.unop a))
    rw [show i.app V.unop (X.presheaf.map f a) =
      Y.presheaf.map ((Opens.map i.base).map f.unop).op (i.app U.unop a)
      from ConcreteCategory.congr_hom (i.naturality f) a]
    exact (differential (i ≫ p)).d_map _ _
  d_app {U} a := by
    change (differential (i ≫ p)).d (i.app U.unop (coefficientOn p U.unop a)) = 0
    rw [coefficientOn_app]
    exact (differential (i ≫ p)).d_app a

/-- Pullback of one-forms, given as a morphism into the direct image. -/
def pullDifferential (i : Y ⟶ X) (p : X ⟶ Spec (CommRingCat.of K)) :
    differentials p ⟶ (Scheme.Modules.pushforward i).obj (differentials (i ≫ p)) :=
  (homDerivationEquiv p _).symm (pullDerivation p i)

theorem pullDifferential_d (i : Y ⟶ X) (p : X ⟶ Spec (CommRingCat.of K))
    (U : X.Opens) (a : Γ(X,U)) :
    (pullDifferential i p).val.app (op U) ((differential p).d a) =
      (differential (i ≫ p)).d (i.app U a) :=
  PresheafOfModules.Derivation.congr_d
    ((homDerivationEquiv p _).apply_symm_apply (pullDerivation p i)) a

/-- Pullback of relative exterior forms, as a morphism into the direct image. -/
def pull (i : Y ⟶ X) (p : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) :
    forms p n ⟶ (Scheme.Modules.pushforward i).obj (forms (i ≫ p) n) :=
  exteriorPull i (pullDifferential i p) n

/-- On wedges of differentials of functions, relative pullback differentiates the
pulled-back functions. -/
theorem pull_wedge_d (i : Y ⟶ X) (p : X ⟶ Spec (CommRingCat.of K)) (n : ℕ)
    (U : X.Opens) (a : Fin n → Γ(X,U)) :
    (pull i p n).val.app (op U) (wedgeSection X.sheaf (differentials p).val n U
      (fun j => (differential p).d (a j))) =
    wedgeSection Y.sheaf (differentials (i ≫ p)).val n (i ⁻¹ᵁ U)
      (fun j => (differential (i ≫ p)).d (i.app U (a j))) := by
  unfold pull wedgeSection
  rw [exteriorPull_section, exteriorMap_wedge]
  apply congrArg (exteriorSection Y.sheaf (differentials (i ≫ p)).val n (i ⁻¹ᵁ U))
  apply congrArg (exteriorPower.ιMulti _ n)
  funext j
  exact pullDifferential_d i p U (a j)

/-- Pulling back relative differentials along a composite agrees with pulling
back first along the second map and then along the first. -/
theorem pullDifferential_comp (j : Z ⟶ Y) (i : Y ⟶ X)
    (p : X ⟶ Spec (CommRingCat.of K)) :
    pullDifferential (j ≫ i) p = CycleQ2ExteriorPullComposition.composeIntoPush j i
      (pullDifferential j (i ≫ p)) (pullDifferential i p) := by
  apply (homDerivationEquiv p _).injective
  ext U a
  change (pullDifferential (j ≫ i) p).val.app (op U.unop) ((differential p).d a) =
    (pullDifferential j (i ≫ p)).val.app (op (i ⁻¹ᵁ U.unop))
      ((pullDifferential i p).val.app (op U.unop) ((differential p).d a))
  simp only [pullDifferential_d] <;> rfl

/-- Pullback of relative exterior forms respects composition on the full sheaf. -/
theorem pull_comp (j : Z ⟶ Y) (i : Y ⟶ X) (p : X ⟶ Spec (CommRingCat.of K)) (n : ℕ) :
    pull (j ≫ i) p n = CycleQ2ExteriorPullComposition.composeIntoPush j i
      (pull j (i ≫ p) n) (pull i p n) := by
  unfold pull
  rw [pullDifferential_comp]
  exact CycleQ2ExteriorPullComposition.exteriorPull_comp j i _ _ n

/-- Over the complex numbers the relative sheaf is the exterior form sheaf
used for the fixed smooth fiber. -/
theorem forms_complex (p : X ⟶ Spec (CommRingCat.of ℂ)) (n : ℕ) :
    forms p n = CycleQ2ExteriorPullComposition.forms X
      (CycleQ2GeometricAffineChartSections.schemeCoefficient p) n := rfl

#print axioms pull_wedge_d
#print axioms pull_comp

end CycleQ2FieldRelativeForms

