import Proposal.GeometricHodgeEulerTangentAtlas
import Proposal.GeometricHodgeEulerTangentLocalization
import Proposal.GeometricHodgeEulerTangentRestriction

/-! The true tangent sheaf of a complex scheme restricts on an affine
finite-presentation chart to the associated module of algebraic derivations.
The comparison uses actual scheme section restriction and the finite
presentation of the Kähler module.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option maxHeartbeats 850000
set_option synthInstance.maxHeartbeats 90000
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerTangentCoherent

open AlgebraicGeometry CategoryTheory Opposite
open CycleQ2HodgeEulerTangentSheaf CycleQ2HodgeEulerTangentAtlas
open CycleQ2HodgeEulerTangentLocalization CycleQ2GeometricChartTangentMaps

variable {X : Scheme.{0}} {A : Type} [CommRing A] [Algebra ℂ A]
  (j : Spec (CommRingCat.of A) ⟶ X) [IsOpenImmersion j]
  (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : j ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

def model : (Spec (CommRingCat.of A)).Modules := (Scheme.Modules.restrictFunctor j).obj (tangent f)

private def imageEquiv {B : Type} [CommRing B] [Algebra ℂ B] [Algebra A B]
    (V : (Spec (CommRingCat.of A)).Opens) (e : (j ''ᵁ V).toScheme ≅ Spec (CommRingCat.of B))
    (hc : e.inv ≫ (j ''ᵁ V).ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ B)))
    (hs : ∀ a, functions e (algebraMap A B a) =
      (j.appIso V).inv ((Spec (CommRingCat.of A)).presheaf.map V.leTop.op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a))) :
    Derivation ℂ B B ≃ₗ[A] (modulesSpecToSheaf.obj (model j f)).obj.obj (op V) := by
  refine { affineTangentEquiv e f hc with map_add' := ?_, map_smul' := ?_ }
  · intro D E
    exact (affineTangentLinearEquiv e f hc).map_add D E
  · intro a D
    let scale (v : Γ(X,j ''ᵁ V)) : Γ(tangent f,j ''ᵁ V) :=
      (CycleQ2GeometricIntrinsicNormal.localLinearHomModule X.sheaf (cotangent f) (functionsModule X) _).smul
        v (tangentSection e f hc D)
    have hD : a • D = (algebraMap A B a) • D := by
      ext x
      change a • D x = algebraMap A B a * D x
      exact Algebra.smul_def a _
    rw [hD]
    change tangentSection e f hc ((algebraMap A B a) • D) =
      scale ((j.appIso V).inv ((Spec (CommRingCat.of A)).presheaf.map V.leTop.op
        ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))
    exact ((affineTangentLinearEquiv e f hc).map_smul (algebraMap A B a) D).trans (congrArg scale (hs a))

def topEquiv : Derivation ℂ A A ≃ₗ[A]
    (moduleSpecΓFunctor (R := CommRingCat.of A)).obj (model j f) :=
  imageEquiv j f ⊤ (topChart j) (topChart_overBase j f h) (functions_topChart j)

def basicEquiv (z : A) : Derivation ℂ (Localization.Away z) (Localization.Away z) ≃ₗ[A]
    (modulesSpecToSheaf.obj (model j f)).obj.obj (op (PrimeSpectrum.basicOpen z)) :=
  imageEquiv j f _ (basicChart j z) (basicChart_overBase j f h z) (functions_basicChart j z)

private theorem restrict_top (z : A) (D : Derivation ℂ A A) :
    (modulesSpecToSheaf.obj (model j f)).obj.map (PrimeSpectrum.basicOpen z).leTop.op
        (topEquiv j f h D) = basicEquiv j f h z (localize (B := Localization.Away z) (Submonoid.powers z) D) := by
  let g := algebraMap A (Localization.Away z)
  have hc : (basicChart j z).inv ≫ (j ''ᵁ PrimeSpectrum.basicOpen z).ι =
      Spec.map (CommRingCat.ofHom g) ≫ (topChart j).inv ≫ (j ''ᵁ ⊤).ι := by
    rw [topChart_inv_ι, basicChart_inv_ι]
  apply (affineTangentEquiv (basicChart j z) f (basicChart_overBase j f h z)).symm.injective
  change recover _ _ _ ((tangent f).val.map (homOfLE (j.image_mono (show PrimeSpectrum.basicOpen z ≤ ⊤
    from le_top))).op (topEquiv j f h D)) = (affineTangentEquiv _ _ _).symm ((affineTangentEquiv _ _ _) _)
  rw [Equiv.symm_apply_apply, localize_eq_extend]
  apply CycleQ2LocalizationDerivation.extend_unique
  intro a
  have H := recover_restriction (topChart j) (basicChart j z) f (topChart_overBase j f h)
    (basicChart_overBase j f h z) (j.image_mono (show PrimeSpectrum.basicOpen z ≤ ⊤ from le_top))
    g hc (topEquiv j f h D) a
  exact H.trans (congrArg (fun E : Derivation ℂ A A => g (E a)) ((affineTangentEquiv _ _ _).left_inv D))

include h in
theorem isLocalizing [Module.FinitePresentation A Ω[A⁄ℂ]] :
    IsLocalizing (modulesSpecToSheaf.obj (model j f)) := by
  intro z
  let S := Submonoid.powers z
  let m := ((modulesSpecToSheaf.obj (model j f)).obj.map (PrimeSpectrum.basicOpen z).leTop.op).hom
  let a := topEquiv j f h
  let b := basicEquiv j f h z
  have he : m ∘ₗ a.toLinearMap = b.toLinearMap ∘ₗ localize (K := ℂ) (B := Localization.Away z) S := by
    ext1 D
    exact restrict_top j f h z D
  apply (IsLocalizedModule.comp_iff_of_bijective_right S a.toLinearMap a.bijective).mp
  rw [he]
  exact IsLocalizedModule.of_linearEquiv S _ b

private def algebraicModuleIso {S : Type} [Ring S] (M N : ModuleCat S) (e : M ≃ N)
    (ha : ∀ x y, e (x + y) = e x + e y) (hs : ∀ (r : S) x, e (r • x) = r • e x) : M ≅ N :=
  LinearEquiv.toModuleIso { e with map_add' := ha, map_smul' := hs }

private def fromTildeIso {S : CommRingCat.{0}} (P : (Spec S).Modules)
    (hP : IsLocalizing (modulesSpecToSheaf.obj P)) :
    tilde ((moduleSpecΓFunctor (R := S)).obj P) ≅ P := by
  letI : IsIso P.fromTildeΓ := (isIso_fromTildeΓ_iff_isLocalizing P).mpr hP
  exact asIso P.fromTildeΓ

/-- A comparison of sheaves, induced by the actual normalized global
derivation and the tilde–global section adjunction. -/
def tildeTangentIso [Module.FinitePresentation A Ω[A⁄ℂ]] :
    tilde (R := CommRingCat.of A) (ModuleCat.of A (Derivation ℂ A A)) ≅ model j f := by
  let a := topEquiv j f h
  let m := algebraicModuleIso (ModuleCat.of A (Derivation ℂ A A))
    ((moduleSpecΓFunctor (R := CommRingCat.of A)).obj (model j f)) a.toEquiv a.map_add a.map_smul
  exact (tilde.functor (CommRingCat.of A)).mapIso m ≪≫ fromTildeIso (model j f) (isLocalizing j f h)

open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold coordinateOpen toBase)
open CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding

def chartTangentIso (φ : CoeffRing →+* ℂ) (i : Fin 4) :
    tilde (R := CommRingCat.of (chart φ i))
        (ModuleCat.of (chart φ i) (RawTangent φ i ⧸ EulerLine φ i)) ≅
      (Scheme.Modules.restrictFunctor ((affineChart φ i).inv ≫ (coordinateOpen φ i).ι)).obj (tangent (toBase φ)) := by
  let e := tangentQuotientEquiv φ i
  let m := algebraicModuleIso (ModuleCat.of (chart φ i) (RawTangent φ i ⧸ EulerLine φ i))
    (ModuleCat.of (chart φ i) (Derivation ℂ (chart φ i) (chart φ i))) e.toEquiv e.map_add e.map_smul
  exact (tilde.functor (CommRingCat.of (chart φ i))).mapIso m ≪≫
    tildeTangentIso _ _ (by rw [Category.assoc]; exact affineChart_overBase φ i)

end CycleQ2HodgeEulerTangentCoherent
end

#print axioms CycleQ2HodgeEulerTangentCoherent.isLocalizing
#print axioms CycleQ2HodgeEulerTangentCoherent.chartTangentIso
