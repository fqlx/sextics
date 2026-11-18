import Proposal.GeometricLiteralThreefoldOrbitActionInclusion
import Proposal.GeometricLiteralThreefoldGradientAtlas

/-! The cyclic substitution on the actual gradient opens of the projective
threefold. Each translated chart is principal at the transformed partial
derivative, including on the charts with a shifted weight-two coordinate.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralThreefoldOrbitAction

open CategoryTheory AlgebraicGeometry MvPolynomial CycleQ2IncidenceDehomogenizedChart
  CycleQ2LiteralAbelJacobiEquations CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientCharts
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralThreefoldResidueFrame CycleQ2LiteralThreefoldGradientAtlas

private theorem partial_substitute (f : ChartPolynomial ℂ →ₐ[ℂ] ChartPolynomial ℂ)
    (k : Option (Fin 3)) (p : ChartPolynomial ℂ) :
    pderiv k (f p) = ∑ l, pderiv k (f (X l)) * f (pderiv l p) := by
  classical
  induction p using MvPolynomial.induction_on with
  | C a =>
    change pderiv k (f (algebraMap ℂ (ChartPolynomial ℂ) a)) = _
    rw [f.commutes]
    simp [MvPolynomial.algebraMap_eq]
  | add p q hp hq => simp only [map_add, hp, hq, mul_add, Finset.sum_add_distrib]
  | mul_X p l hp =>
    have hX : (∑ j, pderiv k (f (X j)) * f (pderiv j (X l))) = pderiv k (f (X l)) := by
      simp [pderiv_X, Pi.single_apply, apply_ite]
    calc
      _ = (∑ j, pderiv k (f (X j)) * f (pderiv j p)) * f (X l) +
          f p * ∑ j, pderiv k (f (X j)) * f (pderiv j (X l)) := by
        rw [map_mul, pderiv_mul, hp, hX]
      _ = _ := by
        rw [Finset.sum_mul, Finset.mul_sum, ← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro j _
        rw [pderiv_mul, map_add, map_mul, map_mul]
        ring

/-- In the shifted coordinates the image partials obey the full chain rule. -/
theorem gradient_action_chain (z : ℂ) (hz : z^3 = 1) (i : Fin 4) (k : Option (Fin 3)) :
    pderiv k (seedF i) =
      ∑ l, pderiv k (chartPolynomialAction z i (X l)) *
        chartPolynomialAction z i (pderiv l (seedF i)) := by
  simpa only [chartPolynomialAction_seedF z hz i] using partial_substitute
    (chartPolynomialAction z i) k (seedF i)

abbrev translatedPatch (z : ℂ) (hz : z^3 = 1) (i j : Fin 4) :=
  Localization.Away (chartAction z hz i (gradient i j))

def gradientPatchAction (z : ℂ) (hz : z^3 = 1) (i j : Fin 4) :
    Patch i j →ₐ[ℂ] translatedPatch z hz i j :=
  IsLocalization.Away.mapₐ _ _ (chartAction z hz i) (gradient i j)

theorem gradientPatchAction_base (z : ℂ) (hz : z^3 = 1) (i j : Fin 4) (x : T i) :
    gradientPatchAction z hz i j (algebraMap _ _ x) =
      algebraMap (T i) (translatedPatch z hz i j) (chartAction z hz i x) := by
  simp only [gradientPatchAction, IsLocalization.Away.mapₐ_apply, IsLocalization.Away.map, IsLocalization.map_eq]
  rfl

theorem gradientOpen_preimage (z : ℂ) (hz : z^3 = 1) (i j : Fin 4) :
    (threefoldAction z hz).hom ⁻¹ᵁ gOpen i j =
      chartInclusion i ''ᵁ PrimeSpectrum.basicOpen (chartAction z hz i (gradient i j)) := by
  let g := (threefoldAction z hz).hom
  let f := chartInclusion i
  have hRange : f.opensRange = fixedOpen i :=
    (Scheme.Hom.opensRange_comp_of_isIso (fixedChart i).hom (fixedOpen i).ι).trans
      (Scheme.Opens.opensRange_ι _)
  have hle : g ⁻¹ᵁ gOpen i j ≤ f.opensRange := by
    rw [hRange, ← fixedOpen_preimage z hz i]
    exact g.preimage_mono (gOpen_le i j)
  have hc : f ⁻¹ᵁ g ⁻¹ᵁ gOpen i j = PrimeSpectrum.basicOpen (chartAction z hz i (gradient i j)) := by
    rw [← Scheme.Hom.comp_preimage, chartInclusion_equivariant, Scheme.Hom.comp_preimage,
      gOpen, Scheme.Hom.preimage_image_eq]
    rfl
  change g ⁻¹ᵁ gOpen i j = f ''ᵁ _
  rw [← hc, Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hle]

theorem gradientPatch_equivariant (z : ℂ) (hz : z^3 = 1) (i j : Fin 4) :
    Spec.map (CommRingCat.ofHom (algebraMap (T i) (translatedPatch z hz i j))) ≫
        chartInclusion i ≫ (threefoldAction z hz).hom =
      Spec.map (CommRingCat.ofHom (gradientPatchAction z hz i j).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap (T i) (Patch i j))) ≫ chartInclusion i := by
  rw [chartInclusion_equivariant, ← Category.assoc, ← Spec.map_comp, ← Category.assoc, ← Spec.map_comp]
  apply congrArg (fun f => Spec.map f ≫ chartInclusion i)
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro a
  exact (gradientPatchAction_base z hz i j a).symm

end CycleQ2LiteralThreefoldOrbitAction
end

#print axioms CycleQ2LiteralThreefoldOrbitAction.gradientOpen_preimage
#print axioms CycleQ2LiteralThreefoldOrbitAction.gradientPatch_equivariant
