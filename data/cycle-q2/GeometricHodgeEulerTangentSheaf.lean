import Proposal.GeometricHodgeEulerChartBinding
import Proposal.GeometricHodgeEulerSequence
import Proposal.GeometricChartTangentMaps

/-!
# Intrinsic tangent sections on affine opens of the weighted sextic

Over a complex affine chart, a section of the dual of the original cotangent
sheaf is determined by its values on the coordinate ring. Pulling back
the universal differential recovers the unique derivation realizing it.
Consequently the ambient Euler quotient describes every section of the
intrinsic tangent sheaf on each of the four weight-one charts.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeEulerTangentSheaf

open AlgebraicGeometry CategoryTheory Opposite
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricDifferentialRestriction
  CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialChartTransport
  CycleQ2GeometricSheafKaehlerMap CycleQ2GeometricIntrinsicNormal
  CycleQ2GeometricChartTangentMaps

variable {X : Scheme.{0}} {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A))
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

abbrev cotangent := differentialSheaf X.sheaf (schemeCoefficient f)
abbrev functionsModule (X : Scheme.{0}) := SheafOfModules.unit (ringSheaf X.sheaf)
abbrev tangent := moduleHomSheaf X.sheaf (cotangent f) (functionsModule X)

/-- The native function ring of the affine open, with its actual chart map. -/
def functions : A ≃+* Γ(X,U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of A)).symm ≪≫ Scheme.Γ.mapIso e.op ≪≫
    U.topIso).commRingCatIsoToRingEquiv

omit [Algebra ℂ A] in
theorem functions_apply (a : A) : functions e a = chartSection e (chartTop U) a :=
  (ConcreteCategory.congr_hom (chartSection_top e) a).symm

abbrev differential (a : A) : Γ(cotangent f,U) :=
  (universalDifferential X.sheaf (schemeCoefficient f)).d (X := op U)
    (chartSection e (chartTop U) a)

abbrev evaluate (s : Γ(tangent f,U)) : Γ(cotangent f,U) →ₗ[Γ(X,U)] Γ(X,U) :=
  localLinearHomEvaluate X.sheaf (cotangent f) (functionsModule X) U s

include h in
theorem section_ext {s t : Γ(tangent f,U)}
    (hs : ∀ a, evaluate f s (differential e f a) = evaluate f t (differential e f a)) : s = t := by
  apply (localLinearHomEquiv X.sheaf (cotangent f) (functionsModule X) U).injective
  apply restrictedLift_unique X.sheaf (schemeCoefficient f) U
  apply chartDerivation_ext e f h
  exact hs

/-- Evaluation on arbitrary algebraic one-forms recovers a chart-linear
functional from a section of the genuine internal Hom. -/
def functional (s : Γ(tangent f,U)) : Ω[A⁄ℂ] →ₗ[A] A where
  toFun ω := (functions e).symm (evaluate f s
    (sectionLift X.sheaf (schemeCoefficient f) (cotangent f)
      (universalDifferential X.sheaf (schemeCoefficient f)) U
      (chartSection e (chartTop U)) (chartSection_complex e f h (chartTop U)) ω))
  map_add' x y := by rw [map_add, map_add, map_add]
  map_smul' a x := by
    rw [sectionLift_smul]
    let c : Γ(X,U) := chartSection e (chartTop U) a
    change (functions e).symm (evaluate f s (c • _)) = _
    rw [(evaluate f s).map_smul]
    change (functions e).symm (c * _) = a * _
    rw [show c = functions e a from (functions_apply e a).symm, map_mul, RingEquiv.symm_apply_apply]

def recover (s : Γ(tangent f,U)) : Derivation ℂ A A :=
  KaehlerDifferential.linearMapEquivDerivation ℂ A (functional e f h s)

theorem recover_apply (s : Γ(tangent f,U)) (a : A) :
    functions e (recover e f h s a) = evaluate f s (differential e f a) := by
  change functions e ((functions e).symm (evaluate f s (sectionLift _ _ _ _ _ _ _
    (KaehlerDifferential.D ℂ A a)))) = _
  rw [RingEquiv.apply_symm_apply, sectionLift_D]
  rfl

theorem evaluate_tangentSection (D : Derivation ℂ A A) (a : A) :
    evaluate f (tangentSection e f h D) (differential e f a) = functions e (D a) :=
  (chartLinearMap_D e f h D (chartTop U) _).trans
    ((chartDerivation_section e f h D (chartTop U) a).trans (functions_apply e _).symm)

/-- Derivations on the affine algebra classify sections of the original
tangent sheaf, including all their components on subopens. -/
def affineTangentEquiv : Derivation ℂ A A ≃ Γ(tangent f,U) where
  toFun := tangentSection e f h
  invFun := recover e f h
  left_inv D := by
    ext a
    apply (functions e).injective
    exact (recover_apply e f h _ a).trans (evaluate_tangentSection e f h D a)
  right_inv s := by
    apply section_ext e f h
    intro a
    exact (evaluate_tangentSection e f h _ a).trans (recover_apply e f h s a)

/-- Linearity uses the actual chart ring isomorphism on coefficients. -/
def affineTangentLinearEquiv :
    letI : Module A Γ(tangent f,U) := Module.compHom _ (functions e).toRingHom
    Derivation ℂ A A ≃ₗ[A] Γ(tangent f,U) := by
  letI : Module A Γ(tangent f,U) := Module.compHom _ (functions e).toRingHom
  refine { affineTangentEquiv e f h with map_add' := ?_, map_smul' := ?_ }
  · intro D E
    apply section_ext e f h
    intro a
    change evaluate f (tangentSection e f h (D + E)) (differential e f a) =
      evaluate f (tangentSection e f h D) (differential e f a) +
        evaluate f (tangentSection e f h E) (differential e f a)
    simp only [evaluate_tangentSection, Derivation.add_apply, map_add]
  · intro r D
    apply section_ext e f h
    intro a
    change evaluate f (tangentSection e f h (r • D)) (differential e f a) =
      X.presheaf.map (𝟙 U).op (functions e r) * evaluate f (tangentSection e f h D) (differential e f a)
    have hid : X.presheaf.map (𝟙 U).op (functions e r) = functions e r :=
      ConcreteCategory.congr_hom (X.presheaf.map_id (op U)) (functions e r)
    rw [hid, evaluate_tangentSection, evaluate_tangentSection, Derivation.smul_apply, smul_eq_mul, map_mul]

open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold coordinateOpen toBase)
open CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding

variable (φ : CoeffRing →+* ℂ) (i : Fin 4)

/-- The Euler quotient computes all tangent-sheaf sections on the original Proj chart. -/
def quotientTangentSections :
    letI : Module (chart φ i) Γ(tangent (toBase φ),coordinateOpen φ i) :=
      Module.compHom _ (functions (affineChart φ i)).toRingHom
    (RawTangent φ i ⧸ EulerLine φ i) ≃ₗ[chart φ i] Γ(tangent (toBase φ),coordinateOpen φ i) := by
  letI : Module (chart φ i) Γ(tangent (toBase φ),coordinateOpen φ i) :=
    Module.compHom _ (functions (affineChart φ i)).toRingHom
  exact (tangentQuotientEquiv φ i).trans
    (affineTangentLinearEquiv (affineChart φ i) (toBase φ) (affineChart_overBase φ i))

theorem quotientTangentSections_coordinate (v : RawTangent φ i) (j : Fin 4) :
    evaluate (toBase φ) (quotientTangentSections φ i (Submodule.Quotient.mk v))
        (differential (affineChart φ i) (toBase φ) (chartMap φ i (MvPolynomial.X j))) =
      functions (affineChart φ i)
        (v.val (i.castSucc.succAbove j) - v.val i.castSucc * radial φ i (i.castSucc.succAbove j)) :=
  (evaluate_tangentSection (affineChart φ i) (toBase φ) (affineChart_overBase φ i)
    (tangentQuotientEquiv φ i (Submodule.Quotient.mk v)) _).trans
    (congrArg (functions (affineChart φ i)) (tangentQuotientEquiv_coordinate φ i v j))

end CycleQ2HodgeEulerTangentSheaf
end

#print axioms CycleQ2HodgeEulerTangentSheaf.affineTangentLinearEquiv
#print axioms CycleQ2HodgeEulerTangentSheaf.quotientTangentSections_coordinate
