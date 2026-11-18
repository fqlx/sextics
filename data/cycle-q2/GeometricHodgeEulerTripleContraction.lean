import Proposal.GeometricHodgeEulerContractionSheaf
import Proposal.GeometricHodgeEulerTangentSheaf
import Proposal.GeometricLiteralAbelJacobiSurfaceWedge

/-!
# Successive contraction of three native vector fields on an affine chart

The first contraction takes a section of the exterior cube to the exterior
square. The second takes it to a one-form, and the third evaluates that
one-form as a regular function. Every affine chart computes this scalar
using the three uniquely recovered derivations of its coordinate algebra.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerTripleContraction

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricIntrinsicNormal CycleQ2LocalSheafificationFrame
  CycleQ2GeometricExteriorLocalFrames CycleQ2LiteralAbelJacobiSurfaceWedge
  CycleQ2HodgeEulerContractionSheaf

variable {X : Scheme.{0}} (M : SheafOfModules.{0} (ringSheaf X.sheaf))

private abbrev raw := exteriorPresheaf X.sheaf.obj M.val 2
private abbrev present := toExteriorSheaf X.sheaf M.val 2

variable (U : X.Opens) (δ : (dual M).val.obj (op U))

private abbrev presentation := @overPresentation (show TopCat from X)
  (ringSheaf X.sheaf) (raw M) U (form M 2) (present M)

local instance presentationInjective :
    PresheafOfModules.IsLocallyInjective ((Opens.grothendieckTopology X).over U)
      (presentation M U) :=
  @overPresentation_locallyInjective (show TopCat from X) (ringSheaf X.sheaf) (raw M) U (form M 2)
    (present M) (exteriorPresentation_locallyInjective X.sheaf M.val 2)

local instance presentationSurjective :
    PresheafOfModules.IsLocallySurjective ((Opens.grothendieckTopology X).over U)
      (presentation M U) :=
  @overPresentation_locallySurjective (show TopCat from X) (ringSheaf X.sheaf) (raw M) U (form M 2)
    (present M) (exteriorPresentation_locallySurjective X.sheaf M.val 2)

private def rawContract : overPresheaf (ringSheaf X.sheaf) (raw M) U ⟶ (M.over U).val where
  app V := ModuleCat.ofHom (contract (R := Γ(X,V.unop.left)) (evaluateOn M U δ V.unop))
  naturality {V W} f := by
    apply ConcreteCategory.hom_ext
    intro x
    change contract (evaluateOn M U δ W.unop)
      (exteriorMap (X.presheaf.map f.unop.left.op).hom (M.val.restrictₛₗ f.unop.left.op) 2 x) =
      M.val.map f.unop.left.op (contract (evaluateOn M U δ V.unop) x)
    apply contract_natural (X.presheaf.map f.unop.left.op).hom (M.val.restrictₛₗ f.unop.left.op)
    intro z
    exact ConcreteCategory.congr_hom (δ.val.naturality f) z

def twoToOneOver : (form M 2).over U ⟶ M.over U where
  val := (PresheafOfModules.homEquivOfIsLocallyBijective
    (presentation M U) (M.over U).isSheaf).symm (rawContract M U δ)

def twoToOne : (form M 2).val.obj (op U) →ₗ[Γ(X,U)] M.val.obj (op U) :=
  ((twoToOneOver M U δ).val.app (op (Over.mk (𝟙 U)))).hom

theorem twoToOneOver_exterior (V : Over U) (x : ⋀[Γ(X,V.left)]^2 (M.val.obj (op V.left))) :
    (twoToOneOver M U δ).val.app (op V) (exteriorSection X.sheaf M.val 2 V.left x) =
      contract (evaluateOn M U δ V) x := by
  have h := (PresheafOfModules.homEquivOfIsLocallyBijective
    (presentation M U) (M.over U).isSheaf).apply_symm_apply (rawContract M U δ)
  exact congrArg (fun f : overPresheaf (ringSheaf X.sheaf) (raw M) U ⟶ (M.over U).val =>
    f.app (op V) x) h

theorem twoToOne_exterior (x : ⋀[Γ(X,U)]^2 (M.val.obj (op U))) :
    twoToOne M U δ (exteriorSection X.sheaf M.val 2 U x) = contract (evaluateOn M U δ (Over.mk (𝟙 U))) x :=
  twoToOneOver_exterior M U δ (Over.mk (𝟙 U)) x

def triple (s t u : (dual M).val.obj (op U)) (ω : (form M 3).val.obj (op U)) : Γ(X,U) :=
  evaluateOn M U u (Over.mk (𝟙 U)) (twoToOne M U t (contractSection M U s ω))

open CycleQ2LiteralThreefoldResidueContraction (interior)
open CycleQ2GeometricDifferentialChartTransport (chartTop)

/-- Evaluating an ordered wedge against three covectors gives the determinant
with those covectors as its rows. -/
theorem covectors_wedge {R N : Type} [CommRing R] [AddCommGroup N] [Module R N]
    (v w u : N →ₗ[R] R) (c : R) (x : Fin 3 → N) :
    u (contract w (interior 2 v (c • exteriorPower.ιMulti R 3 x))) =
      c * (Matrix.of ![fun j => v (x j), fun j => w (x j), fun j => u (x j)]).det := by
  have h₀ : (0 : Fin 3).removeNth x = ![x 1, x 2] := by funext j; fin_cases j <;> rfl
  have h₁ : (1 : Fin 3).removeNth x = ![x 0, x 2] := by funext j; fin_cases j <;> rfl
  have h₂ : (2 : Fin 3).removeNth x = ![x 0, x 1] := by funext j; fin_cases j <;> rfl
  rw [map_smul, map_smul, map_smul, smul_eq_mul]
  congr 1
  rw [CycleQ2LiteralThreefoldResidueContraction.interior_wedge, Fin.sum_univ_three, h₀, h₁, h₂,
    Matrix.det_fin_three]
  change _ = v (x 0) * w (x 1) * u (x 2) -
    v (x 0) * w (x 2) * u (x 1) -
    v (x 1) * w (x 0) * u (x 2) +
    v (x 1) * w (x 2) * u (x 0) +
    v (x 2) * w (x 0) * u (x 1) -
    v (x 2) * w (x 1) * u (x 0)
  norm_num [map_smul, contract_wedge, smul_eq_mul] <;> ring

/-- Native regular-function value of the triple contraction on a decomposable section. -/
theorem triple_exterior_wedge (s t u : (dual M).val.obj (op U)) (c : Γ(X,U))
    (x : Fin 3 → M.val.obj (op U)) :
    triple M U s t u (exteriorSection X.sheaf M.val 3 U (c • exteriorPower.ιMulti (Γ(X,U)) 3 x)) =
      c * (Matrix.of ![fun j => evaluateOn M U s (chartTop U) (x j),
        fun j => evaluateOn M U t (chartTop U) (x j), fun j => evaluateOn M U u (chartTop U) (x j)]).det := by
  rw [triple, contractSection_exterior, twoToOne_exterior]
  exact covectors_wedge _ _ _ c x

section Chart
open CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialRestriction
  CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricSheafKaehlerMap
  CycleQ2GeometricChartTangentMaps CycleQ2ChartExteriorBinding CycleQ2ExteriorSectionNaturality
  CycleQ2HodgeEulerTangentSheaf
open CycleQ2LiteralThreefoldResidueContraction (interior)
open scoped KaehlerDifferential

variable {O : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : O.toScheme ≅ Spec (CommRingCat.of A)) (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ O.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

def affineScalar (v w u : Derivation ℂ A A) (ω : ⋀[A]^3 Ω[A⁄ℂ]) : A :=
  u.liftKaehlerDifferential (contract w.liftKaehlerDifferential (interior 2 v.liftKaehlerDifferential ω))

/-- Successive contractions in the order v, w, u give the positive determinant
whose rows are their evaluations on the ordered one-forms. -/
theorem affineScalar_wedge (v w u : Derivation ℂ A A) (c : A) (x : Fin 3 → Ω[A⁄ℂ]) :
    affineScalar v w u (c • exteriorPower.ιMulti A 3 x) = c *
      (Matrix.of ![fun j => v.liftKaehlerDifferential (x j),
        fun j => w.liftKaehlerDifferential (x j), fun j => u.liftKaehlerDifferential (x j)]).det :=
  covectors_wedge _ _ _ c x

theorem affineScalar_coordinateWedge (v w u : Derivation ℂ A A) (c : A) (x : Fin 3 → A) :
    affineScalar v w u (c • exteriorPower.ιMulti A 3 (fun j => KaehlerDifferential.D ℂ A (x j))) =
      c * (Matrix.of ![fun j => v (x j), fun j => w (x j), fun j => u (x j)]).det := by
  simpa only [Derivation.liftKaehlerDifferential_comp_D] using
    affineScalar_wedge v w u c (fun j => KaehlerDifferential.D ℂ A (x j))

theorem triple_tangentSection (v w u : Derivation ℂ A A) (ω : ⋀[A]^3 Ω[A⁄ℂ]) :
    triple (cotangent f) O (tangentSection e f h v) (tangentSection e f h w) (tangentSection e f h u)
      (chartExteriorSheafSection e f h 3 (chartTop O) ω) = functions e (affineScalar v w u ω) := by
  rw [triple, contractSection_chart, functions_apply]
  let N := cotangent f
  let g := chartSection e (chartTop O)
  let L := sectionLiftSemilinear X.sheaf (schemeCoefficient f) N
    (universalDifferential X.sheaf (schemeCoefficient f)) O g (chartSection_complex e f h (chartTop O))
  let η := interior 2 v.liftKaehlerDifferential ω
  change evaluateOn N O (tangentSection e f h u) (chartTop O)
    (twoToOne N O (tangentSection e f h w) (exteriorSection X.sheaf N.val 2 O (exteriorMap g L 2 η))) = _
  rw [twoToOne_exterior]
  have hw := contract_natural g L w.liftKaehlerDifferential (evaluateOn N O (tangentSection e f h w) (chartTop O))
    (tangentSection_on_form e f h w) η
  exact (congrArg (evaluateOn N O (tangentSection e f h u) (chartTop O)) hw).trans
    (tangentSection_on_form e f h u (contract w.liftKaehlerDifferential η))

/-- The scalar from three arbitrary actual tangent sections in the native affine chart. -/
theorem triple_chart (s t u : Γ(tangent f,O)) (ω : ⋀[A]^3 Ω[A⁄ℂ]) :
    triple (cotangent f) O s t u (chartExteriorSheafSection e f h 3 (chartTop O) ω) =
      functions e (affineScalar (recover e f h s) (recover e f h t) (recover e f h u) ω) := by
  have hs (d : Γ(tangent f,O)) : tangentSection e f h (recover e f h d) = d :=
    (affineTangentEquiv e f h).apply_symm_apply d
  simpa only [hs] using triple_tangentSection e f h (recover e f h s) (recover e f h t) (recover e f h u) ω

end Chart
end CycleQ2HodgeEulerTripleContraction
end

#print axioms CycleQ2HodgeEulerTripleContraction.triple_exterior_wedge
#print axioms CycleQ2HodgeEulerTripleContraction.twoToOne_exterior
#print axioms CycleQ2HodgeEulerTripleContraction.triple_chart

#print axioms CycleQ2HodgeEulerTripleContraction.affineScalar_coordinateWedge
