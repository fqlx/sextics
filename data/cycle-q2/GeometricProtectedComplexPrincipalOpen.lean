import Proposal.GeometricProtectedComplexChart
import Proposal.GeometricRegularDeRham
import Mathlib.RingTheory.Jacobson.Ring
import Mathlib.RingTheory.Localization.Away.AdjoinRoot
import Mathlib.Analysis.Complex.Polynomial.Basic

/-!
# Complex points of the principal opens in the protected de Rham complex

A point has five affine coordinates, satisfies the protected equation,
and has nonzero values of the normal derivative and the specified regular
function. Evaluation identifies these points with complex algebra maps
from the twice-localized coordinate ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2ProtectedComplexPrincipalOpen

open MvPolynomial HodgeComputer CycleQ2AffineClearing CycleQ2AffineHypersurface
open CycleQ2ProtectedComplexChart CycleQ2GeometricRegularDeRham CategoryTheory

/-- Evaluation on the quotient by the protected affine equation. -/
def baseEval (x : AffineHypersurface) : BaseRing →ₐ[ℂ] ℂ :=
  Ideal.Quotient.liftₐ _ (aeval x.val) (by
    intro P hP
    obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton.mp hP
    exact (map_mul _ _ _).trans (by rw [show aeval x.val affineF = 0 from x.property, zero_mul]))

@[simp] theorem baseEval_projection (x : AffineHypersurface) (P : AmbientPoly 4) :
    baseEval x (affineProjection P) = eval x.val P := rfl

private def polynomialAt (φ : BaseRing →ₐ[ℂ] ℂ) : AmbientPoly 4 →ₐ[ℂ] ℂ :=
  φ.comp (Ideal.Quotient.mkₐ ℂ (Ideal.span {affineF}))

private def pointOfBaseHom (φ : BaseRing →ₐ[ℂ] ℂ) : AffineHypersurface :=
  ⟨polynomialAt φ ∘ X, by
    change aeval (polynomialAt φ ∘ X) affineF = 0
    rw [← aeval_unique (polynomialAt φ)]
    change φ (affineProjection affineF) = 0
    rw [(affineProjection_kernel _).mpr dvd_rfl, map_zero]⟩

/-- The affine coordinates are recovered by evaluating the five generators. -/
def baseEquiv : AffineHypersurface ≃ (BaseRing →ₐ[ℂ] ℂ) where
  toFun := baseEval
  invFun := pointOfBaseHom
  left_inv x := by
    apply Subtype.ext
    funext i
    change baseEval x (affineProjection (X i)) = x.val i
    simp
  right_inv φ := by
    apply AlgHom.ext
    intro a
    obtain ⟨P, rfl⟩ := affineProjection_surjective a
    change aeval (polynomialAt φ ∘ X) P = polynomialAt φ P
    rw [← aeval_unique (polynomialAt φ)]

private theorem away_lift_compute {R : Type} [CommRing R] [Algebra ℂ R] (t : R)
    (φ : R →ₐ[ℂ] ℂ) (h : IsUnit (φ t)) (a : R) :
    IsLocalization.Away.liftAlgHom t (S := Localization.Away t) (f := φ) h
      (algebraMap R (Localization.Away t) a) = φ a :=
  IsLocalization.Away.lift_eq t (S := Localization.Away t) (g := φ.toRingHom) h a

/-- The universal property of a principal localization on complex points. -/
private def awayEquiv {R : Type} [CommRing R] [Algebra ℂ R] (t : R) :
    {φ : R →ₐ[ℂ] ℂ // φ t ≠ 0} ≃ (Localization.Away t →ₐ[ℂ] ℂ) where
  toFun φ := IsLocalization.Away.liftAlgHom t (f := φ.val) (isUnit_iff_ne_zero.mpr φ.property)
  invFun ψ := ⟨ψ.comp (Algebra.algHom ℂ R _), by
    change ψ (algebraMap R (Localization.Away t) t) ≠ 0
    exact ((IsLocalization.Away.algebraMap_isUnit t (S := Localization.Away t)).map ψ).ne_zero⟩
  left_inv φ := by
    apply Subtype.ext
    apply AlgHom.ext
    intro a
    exact away_lift_compute t φ.val (isUnit_iff_ne_zero.mpr φ.property) a
  right_inv ψ := by
    apply IsLocalization.algHom_ext (Submonoid.powers t)
    apply AlgHom.ext
    intro a
    exact away_lift_compute t (ψ.comp (Algebra.algHom ℂ R _))
      ((IsLocalization.Away.algebraMap_isUnit t (S := Localization.Away t)).map ψ) a

abbrev NormalPoints := {x : AffineHypersurface // eval x.val (pderiv 0 affineF) ≠ 0}

/-- Evaluation on the normal-Jacobian open extends the quotient-ring evaluation. -/
def normalEquiv : NormalPoints ≃ (OpenRing →ₐ[ℂ] ℂ) :=
  (baseEquiv.subtypeEquiv (q := fun φ => φ normalClass ≠ 0) (fun _ => Iff.rfl)).trans
    (awayEquiv normalClass)

def openEval (x : NormalPoints) : OpenRing →ₐ[ℂ] ℂ := normalEquiv x

@[simp] theorem openEval_algebraMap (x : NormalPoints) (a : BaseRing) :
    openEval x (algebraMap BaseRing OpenRing a) = baseEval x.val a :=
  away_lift_compute normalClass (baseEval x.val) (isUnit_iff_ne_zero.mpr x.property) a

/-- Complex points of the further principal open defined by the regular function s. -/
abbrev PrincipalPoints (s : OpenRing) := {x : NormalPoints // openEval x s ≠ 0}

def principalEquiv (s : OpenRing) : PrincipalPoints s ≃ (LocalRing s →ₐ[ℂ] ℂ) :=
  (normalEquiv.subtypeEquivOfSubtype (p := fun φ => φ s ≠ 0)).trans (awayEquiv s)

def localEval {s : OpenRing} (x : PrincipalPoints s) : LocalRing s →ₐ[ℂ] ℂ :=
  principalEquiv s x

@[simp] theorem localEval_algebraMap {s : OpenRing} (x : PrincipalPoints s) (a : OpenRing) :
    localEval x (algebraMap OpenRing (LocalRing s) a) = openEval x.val a :=
  away_lift_compute s (openEval x.val) (isUnit_iff_ne_zero.mpr x.property) a

@[simp] theorem localEval_polynomial {s : OpenRing} (x : PrincipalPoints s) (P : AmbientPoly 4) :
    localEval x (localPolynomial s P) = eval x.val.val.val P := by
  rw [localPolynomial, localEval_algebraMap, polynomialValue, openEval_algebraMap, baseEval_projection]

/-- The nonzero denominators of the protected existential statement give
nonempty complex domains. A maximal residue field of the localization is
a finite extension of the complex numbers by Zariski's lemma. -/
theorem principalPoints_nonempty_iff (s : OpenRing) : Nonempty (PrincipalPoints s) ↔ s ≠ 0 := by
  constructor
  · rintro ⟨x⟩ rfl
    exact x.property (map_zero _)
  · intro hs
    let : IsDomain (LocalRing s) := Localization.Away.isDomain hs
    obtain ⟨M, hM⟩ := Ideal.exists_maximal (LocalRing s)
    let : Field (LocalRing s ⧸ M) := Ideal.Quotient.field M
    let : Module.Finite ℂ (LocalRing s ⧸ M) :=
      finite_of_finite_type_of_isJacobsonRing ℂ _
    let φ : (LocalRing s ⧸ M) →ₐ[ℂ] ℂ := IsAlgClosed.lift
    exact ⟨(principalEquiv s).symm (φ.comp (Ideal.Quotient.mkₐ ℂ M))⟩

/-- Inclusion in the affine hypersurface with its usual complex topology. -/
def inclusion (s : OpenRing) : C(PrincipalPoints s, AffineHypersurface) :=
  ⟨fun x => x.val.val, continuous_subtype_val.comp continuous_subtype_val⟩

def principalInclusion (s : OpenRing) : TopCat.of (PrincipalPoints s) ⟶ AffineHypersurface :=
  TopCat.ofHom (inclusion s)

private theorem continuous_away_eval {X R S : Type} [TopologicalSpace X]
    [CommRing R] [CommRing S] [Algebra R S] (d : R) [IsLocalization.Away d S]
    (q : X → R →+* ℂ) (v : X → S →+* ℂ)
    (hv : ∀ x a, v x (algebraMap R S a) = q x a)
    (hq : ∀ a, Continuous (fun x => q x a)) (hd : ∀ x, q x d ≠ 0) (r : S) :
    Continuous (fun x => v x r) := by
  obtain ⟨n, a, ha⟩ := IsLocalization.Away.surj d r
  have h : (fun x => v x r) = fun x => q x a / q x d ^ n := by
    funext x
    apply (eq_div_iff (pow_ne_zero n (hd x))).mpr
    simpa only [map_mul, map_pow, hv] using congrArg (v x) ha
  rw [h]
  exact (hq a).div ((hq d).pow n) (fun x => pow_ne_zero n (hd x))

theorem continuous_baseEval (a : BaseRing) :
    Continuous (fun x : AffineHypersurface => baseEval x a) := by
  obtain ⟨P, rfl⟩ := affineProjection_surjective a
  simp only [baseEval_projection]
  exact
    (MvPolynomial.continuous_eval P).comp'
      (continuous_subtype_val : Continuous (fun x : AffineHypersurface => x.val))

theorem continuous_openEval (a : OpenRing) :
    Continuous (fun x : NormalPoints => openEval x a) := by
  apply continuous_away_eval normalClass (fun x : NormalPoints => (baseEval x.val).toRingHom)
    (fun x => (openEval x).toRingHom) openEval_algebraMap
  · exact fun b => (continuous_baseEval b).comp continuous_subtype_val
  · intro x
    change baseEval x.val (affineProjection (pderiv 0 affineF)) ≠ 0
    rw [baseEval_projection]
    exact x.property

theorem continuous_localEval (s : OpenRing) (a : LocalRing s) :
    Continuous (fun x : PrincipalPoints s => localEval x a) := by
  apply continuous_away_eval s (fun x : PrincipalPoints s => (openEval x.val).toRingHom)
    (fun x => (localEval x).toRingHom) localEval_algebraMap
  · exact fun b => (continuous_openEval b).comp continuous_subtype_val
  · exact fun x => x.property

theorem inclusion_isOpenEmbedding (s : OpenRing) : Topology.IsOpenEmbedding (inclusion s) := by
  have hn : IsOpen {x : AffineHypersurface | eval x.val (pderiv 0 affineF) ≠ 0} :=
    isOpen_ne_fun ((MvPolynomial.continuous_eval _).comp continuous_subtype_val) continuous_const
  have hs : IsOpen {x : NormalPoints | openEval x s ≠ 0} :=
    isOpen_ne_fun (continuous_openEval s) continuous_const
  exact hn.isOpenEmbedding_subtypeVal.comp hs.isOpenEmbedding_subtypeVal

end CycleQ2ProtectedComplexPrincipalOpen
end

#print axioms CycleQ2ProtectedComplexPrincipalOpen.inclusion_isOpenEmbedding
#print axioms CycleQ2ProtectedComplexPrincipalOpen.continuous_localEval
#print axioms CycleQ2ProtectedComplexPrincipalOpen.principalPoints_nonempty_iff
#print axioms CycleQ2ProtectedComplexPrincipalOpen.principalEquiv
#print axioms CycleQ2ProtectedComplexPrincipalOpen.localEval_polynomial
