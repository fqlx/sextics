import Proposal.GeometricHodgeEulerTangentAtlas
import Proposal.GeometricHodgeEulerContractionCharts
import Proposal.GeometricHodgeThreefoldGradient
import Proposal.GeometricHodgeThreefoldProper

/-! # The sixteen principal gradient opens of the original moving hypersurface

In each weight-one chart the four dehomogenized partials generate the unit
ideal on the good parameter open. Their principal opens refine the projective
coordinate cover. Their affine coordinate rings are the gradient localizations
carrying the normalized residue.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeGradientAtlas
open CategoryTheory AlgebraicGeometry
  CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding CycleQ2HodgeEulerTangentAtlas
  CycleQ2HodgeEulerContractionCharts CycleQ2GeometricHodgeThreefold CycleQ2GenericSexticGradient

variable (φ : CoeffRing →+* ℂ) (i j : Fin 4)

abbrev inclusion := (affineChart φ i).inv ≫ (coordinateOpen φ i).ι
abbrev U : (threefold φ).Opens := inclusion φ i ''ᵁ PrimeSpectrum.basicOpen (gradientEntry (F φ i) j)
abbrev atlas := basicChart (inclusion φ i) (gradientEntry (F φ i) j)

theorem atlas_inv_ι : (atlas φ i j).inv ≫ (U φ i j).ι =
    Spec.map (CommRingCat.ofHom (patchMap (F φ i) j).toRingHom) ≫ inclusion φ i :=
  basicChart_inv_ι (inclusion φ i) _

theorem atlas_overBase : (atlas φ i j).inv ≫ (U φ i j).ι ≫ toBase φ =
    Spec.map (CommRingCat.ofHom (algebraMap ℂ (Patch (F φ i) j))) :=
  basicChart_overBase (inclusion φ i) (toBase φ)
    (by rw [inclusion, Category.assoc, affineChart_overBase]) _

theorem inclusion_range : (inclusion φ i).opensRange = coordinateOpen φ i :=
  (Scheme.Hom.opensRange_comp_of_isIso (affineChart φ i).inv (coordinateOpen φ i).ι).trans
    (Scheme.Opens.opensRange_ι _)

theorem U_le : U φ i j ≤ coordinateOpen φ i :=
  ((inclusion φ i).image_le_opensRange _).trans (inclusion_range φ i).le

theorem chart_cover (hg : IsUnit (φ gradientOpen)) : (⨆ j, U φ i j) = coordinateOpen φ i := by
  have hc : (⨆ j, PrimeSpectrum.basicOpen (gradientEntry (F φ i) j)) = ⊤ :=
    PrimeSpectrum.iSup_basicOpen_eq_top_iff.mpr (chartGradient_span φ hg i)
  change (⨆ j, inclusion φ i ''ᵁ PrimeSpectrum.basicOpen (gradientEntry (F φ i) j)) = _
  rw [← Scheme.Hom.image_iSup, hc, Scheme.Hom.image_top_eq_opensRange, inclusion_range]

theorem cover_iterated (hg : IsUnit (φ goodParameter)) : (⨆ i, ⨆ j, U φ i j) = ⊤ := by
  have h : IsUnit (φ gradientOpen) := by
    rw [goodParameter, map_mul, IsUnit.mul_iff] at hg
    exact hg.1
  simp only [chart_cover φ _ h, coordinateOpens_cover_of_good φ hg]

theorem cover (hg : IsUnit (φ goodParameter)) : (⨆ a : Fin 4 × Fin 4, U φ a.1 a.2) = ⊤ := by
  simpa only [iSup_prod] using cover_iterated φ hg

end CycleQ2HodgeGradientAtlas
end
#print axioms CycleQ2HodgeGradientAtlas.cover
