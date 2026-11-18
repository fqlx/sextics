import Proposal.GeometricHodgeEulerTangentAtlas
import Proposal.GeometricHodgeEulerTangentRestriction
import Proposal.GeometricHodgeEulerTangentCoordinates
import Proposal.GeometricHodgeEulerLocalizedGradient

/-!
# Coordinate evaluation on every principal open of a weight-one chart

An intrinsic tangent section is determined by its four values on the
normalized coordinate differentials. Their one relation is the normalized
gradient of the original hypersurface. Every tuple satisfying that
relation arises on the principal open, including at singular points.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeEulerBasicDerivativeFrame

open AlgebraicGeometry CategoryTheory Opposite MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding
open CycleQ2HodgeEulerSheaf CycleQ2HodgeEulerTangentAtlas CycleQ2HodgeEulerTangentCoordinates
open CycleQ2HodgeTwistRatios (normalized)
open CycleQ2HodgeEulerTangentSheaf CycleQ2GeometricAffineChartSections
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricDifferentialChartTransport

private def mapKernel {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (g : Fin 4 → A) (g' : Fin 4 → B) (h : ∀ j, e (g j) = g' j)
    (v : (pairing g).ker) : (pairing g').ker := by
  refine ⟨fun j => e (v.val j), ?_⟩
  have hv : ∑ l, g l * v.val l = 0 := (pairing_apply g v.val).symm.trans v.property
  rw [LinearMap.mem_ker, pairing_apply]
  simpa only [map_sum, map_mul, h, map_zero] using congrArg e hv

private def kernelEquiv {A B : Type*} [CommRing A] [CommRing B] (e : A ≃+* B)
    (g : Fin 4 → A) (g' : Fin 4 → B) (h : ∀ j, e (g j) = g' j) :
    (pairing g).ker ≃ (pairing g').ker where
  toFun := mapKernel e g g' h
  invFun := mapKernel e.symm g' g (fun j => by rw [← h, RingEquiv.symm_apply_apply])
  left_inv v := Subtype.ext (funext fun j => e.symm_apply_apply (v.val j))
  right_inv v := Subtype.ext (funext fun j => e.apply_symm_apply (v.val j))

variable (φ : CoeffRing →+* ℂ) (i : Fin 4) (z : chart φ i)

abbrev inclusion : Spec (CommRingCat.of (chart φ i)) ⟶ threefold φ :=
  (affineChart φ i).inv ≫ (coordinateOpen φ i).ι

abbrev principalOpen : (threefold φ).Opens :=
  inclusion φ i ''ᵁ PrimeSpectrum.basicOpen z

theorem principalOpen_le : principalOpen φ i z ≤ coordinateOpen φ i := by
  apply ((inclusion φ i).image_le_opensRange _).trans
  exact ((Scheme.Hom.opensRange_comp_of_isIso (affineChart φ i).inv (coordinateOpen φ i).ι).trans
    (Scheme.Opens.opensRange_ι _)).le

private abbrev B := Localization.Away z
private abbrev e := basicChart (inclusion φ i) z

private theorem chart_overBase : (e φ i z).inv ≫ (principalOpen φ i z).ι ≫ toBase φ =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (B φ i z))) :=
  basicChart_overBase (inclusion φ i) (toBase φ)
    (by rw [inclusion, Category.assoc, affineChart_overBase]) z

private theorem functions_image (a : chart φ i) :
    functions (e φ i z) (algebraMap (chart φ i) (B φ i z) a) =
      chartSection (affineChart φ i) (Over.mk (homOfLE (principalOpen_le φ i z))) a := by
  let h := principalOpen_le φ i z
  let j := homOfLE h
  have hr := functions_restrict (affineChart φ i) (e φ i z) h
    (algebraMap (chart φ i) (B φ i z)) (basicChart_inv_ι (inclusion φ i) z) a
  have hn := chartSection_naturality (affineChart φ i)
    (Over.homMk j : Over.mk j ⟶ Over.mk (𝟙 (coordinateOpen φ i))) a
  exact hr.symm.trans ((congrArg ((threefold φ).presheaf.map j.op)
    (functions_apply (affineChart φ i) a)).trans hn)

abbrev normalizedGradient (l : Fin 4) : Γ(threefold φ, principalOpen φ i z) :=
  normalized φ i (partialValue φ (i.castSucc.succAbove l)) (partial_mem φ _)
    (principalOpen φ i z) (principalOpen_le φ i z)

private theorem functions_gradient (l : Fin 4) :
    functions (e φ i z) (CycleQ2HodgeEulerLocalizedGradient.gradientRow (F φ i) (B φ i z) l) =
      normalizedGradient φ i z l := by
  change functions (e φ i z) (algebraMap _ _ (chartMap φ i (pderiv l (F φ i)))) = _
  rw [functions_image, ← partial_succAbove]
  exact chartSection_partial φ i (principalOpen φ i z) (principalOpen_le φ i z) (i.castSucc.succAbove l)

private theorem functions_coordinate (l : Fin 4) :
    functions (e φ i z) (algebraMap (chart φ i) (B φ i z) (chartMap φ i (X l))) =
      normalized φ i (coord φ (i.castSucc.succAbove l)) (coord_mem_grade φ _)
        (principalOpen φ i z) (principalOpen_le φ i z) := by
  rw [functions_image]
  have h := chartSection_coordinate φ i (principalOpen φ i z) (principalOpen_le φ i z) (i.castSucc.succAbove l)
  simpa only [coordinate, dehom_X_succAbove] using h

/-- On a principal subopen the native gradient relation is the only relation
on the four intrinsic coordinate derivatives. -/
def basicDerivativeFrame : Γ(tangent (toBase φ), principalOpen φ i z) ≃
    (pairing (normalizedGradient φ i z)).ker :=
  (affineTangentEquiv (e φ i z) (toBase φ) (chart_overBase φ i z)).symm.trans
    ((CycleQ2HodgeEulerLocalizedGradient.derivationEquiv (F φ i) (Submonoid.powers z)
      (B φ i z)).toEquiv.trans (kernelEquiv (functions (e φ i z)) _ _ (functions_gradient φ i z)))

theorem basicDerivativeFrame_apply (s : Γ(tangent (toBase φ), principalOpen φ i z)) (l : Fin 4) :
    (basicDerivativeFrame φ i z s).val l =
      evaluate (toBase φ) s ((universalDifferential (threefold φ).sheaf (schemeCoefficient (toBase φ))).d
        (X := op (principalOpen φ i z)) (normalized φ i (coord φ (i.castSucc.succAbove l))
          (coord_mem_grade φ _) (principalOpen φ i z) (principalOpen_le φ i z))) := by
  let a := algebraMap (chart φ i) (B φ i z) (chartMap φ i (X l))
  change functions (e φ i z) (recover (e φ i z) (toBase φ) (chart_overBase φ i z) s a) = _
  rw [recover_apply]
  apply congrArg (evaluate (toBase φ) s)
  apply congrArg ((universalDifferential (threefold φ).sheaf (schemeCoefficient (toBase φ))).d
    (X := op (principalOpen φ i z)))
  exact (functions_apply (e φ i z) a).symm.trans (functions_coordinate φ i z l)

end CycleQ2HodgeEulerBasicDerivativeFrame
end

#print axioms CycleQ2HodgeEulerBasicDerivativeFrame.basicDerivativeFrame_apply
