import Proposal.GeometricHodgeEulerTangentAtlas
import Proposal.GeometricHodgeEulerTangentCoordinates
import Proposal.GeometricHodgeEulerContractionCharts
import Proposal.GeometricSurfaceOverlap

/-!
# Units on a principal gradient chart

The derivative selecting an affine gradient patch is a unit on every smaller
open. The affine-chart comparison identifies that unit with the homogeneous
partial normalized at the same pivot.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2WeightedOwnGradientUnit

open CategoryTheory AlgebraicGeometry
open CycleQ2GeometricAffineChartSections CycleQ2GeometricPrincipalChartSections
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding
open CycleQ2HodgeEulerContractionCharts CycleQ2HodgeEulerTangentAtlas
open CycleQ2HodgeEulerTangentCoordinates CycleQ2HodgeEulerSheaf
open CycleQ2HodgeTwistRatios (normalized)
open CycleQ2GenericSexticGradient (CoeffRing)

variable {k : Type} [CommRing k] (φ : CoeffRing →+* k)
  (a : Fin 4 × Fin 4) (W : (threefold φ).Opens)

private abbrev incl := (affineChart φ a.1).inv ≫ (coordinateOpen φ a.1).ι
private abbrev patch := incl φ a ''ᵁ PrimeSpectrum.basicOpen (gradientEntry (F φ a.1) a.2)

theorem own_chart_gradient_unit (hW : W ≤ patch φ a) (hi : W ≤ coordinateOpen φ a.1) :
    IsUnit (chartSection (affineChart φ a.1) (Over.mk (homOfLE hi))
      (conePartial φ a.1 (a.1.castSucc.succAbove a.2))) := by
  let g := gradientEntry (F φ a.1) a.2
  have hinc : patch φ a ≤ coordinateOpen φ a.1 :=
    ((incl φ a).image_le_opensRange _).trans
      (((Scheme.Hom.opensRange_comp_of_isIso (affineChart φ a.1).inv
        (coordinateOpen φ a.1).ι).trans (Scheme.Opens.opensRange_ι _)).le)
  let e := basicChart (incl φ a) g
  have hc := chartSection_compatible (affineChart φ a.1) e hinc
    (algebraMap (chart φ a.1) (Localization.Away g))
    (basicChart_inv_ι (incl φ a) g) (Over.mk (homOfLE hW)) g
  rw [partial_succAbove]
  change IsUnit (chartSection (affineChart φ a.1) (Over.mk (homOfLE hi)) g)
  rw [← hc]
  exact (IsLocalization.Away.algebraMap_isUnit (S := Localization.Away g) g).map
    (chartSection e (Over.mk (homOfLE hW)))

theorem own_gradient_unit (hW : W ≤ patch φ a) (hi : W ≤ coordinateOpen φ a.1) :
    IsUnit (normalized φ a.1 (partialValue φ (a.1.castSucc.succAbove a.2))
      (partial_mem φ _) W hi) := by
  rw [← chartSection_partial φ a.1 W hi]
  exact own_chart_gradient_unit φ a W hW hi

end CycleQ2WeightedOwnGradientUnit
end

#print axioms CycleQ2WeightedOwnGradientUnit.own_gradient_unit
