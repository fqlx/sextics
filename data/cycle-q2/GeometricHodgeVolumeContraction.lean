import Proposal.GeometricHodgeVolumeContractionPatch
import Proposal.GeometricHodgeVolumeContractionGluing
import Proposal.GeometricHodgeEulerVolume
import Proposal.GeometricHodgeGradientAtlas
import Proposal.GeometricHodgeEulerTangentSheaf

/-!
# The tangent-to-two-forms isomorphism on the original moving threefold

The global Poincaré residue restricts on the sixteen gradient opens to
the signed wedge of three Kähler coordinates divided by a unit partial.
Contracting the genuine tangent sheaf with this specific form identifies
it with the second exterior cotangent sheaf. The section formula holds on
every open of the projective threefold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 800000
set_option maxRecDepth 4000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeVolumeContraction

open CategoryTheory Opposite AlgebraicGeometry MvPolynomial
open CycleQ2GenericSexticGradient CycleQ2GeometricHodgeThreefold CycleQ2HodgeEuler
  CycleQ2HodgeGradientAtlas CycleQ2HodgeEulerContractionCharts CycleQ2HodgeEulerContractionSheaf
  CycleQ2HodgeEulerVolumeChart CycleQ2GeometricAffineChartSections CycleQ2ChartExteriorBinding
  CycleQ2ExteriorSectionNaturality

variable (φ : CoeffRing →+* ℂ) (hg : IsUnit (φ goodParameter))

private abbrev D (a : Fin 4 × Fin 4) := U φ a.1 a.2
private abbrev N := oneForms (toBase φ)

private def onPatch (a : Fin 4 × Fin 4) : (dual (N φ)).over (D φ a) ≅ (form (N φ) 2).over (D φ a) :=
  patchIso (atlas φ a.1 a.2) (toBase φ) (atlas_overBase φ a.1 a.2)
    (basis (F φ a.1) a.2) (volumeUnit φ a.1 a.2)

private theorem onPatch_apply (a : Fin 4 × Fin 4) (V : (threefold φ).Opens)
    (hi : V ≤ D φ a) (δ : (dual (N φ)).val.obj (op V)) :
    (onPatch φ a).hom.val.app (op (Over.mk (homOfLE hi))) δ = contractSection (N φ) V δ
      ((form (N φ) 3).val.map (homOfLE (le_top : V ≤ ⊤)).op (CycleQ2HodgeEulerVolume.omega φ hg)) := by
  unfold onPatch
  apply patchIso_apply_of_volume
  rw [← projectiveResidue_eq_frame φ a.1 a.2]
  exact CycleQ2HodgeEulerVolume.omega_on_gradient φ hg a.1 a.2
    (U_le φ a.1 a.2) (atlas φ a.1 a.2) (atlas_overBase φ a.1 a.2) (atlas_inv_ι φ a.1 a.2)

def volumeIso : CycleQ2HodgeEulerTangentSheaf.tangent (toBase φ) ≅ form (N φ) 2 :=
  gluedIso (N φ) (CycleQ2HodgeEulerVolume.omega φ hg) (D φ) (cover φ hg)
    (onPatch φ) (onPatch_apply φ hg)

theorem volumeIso_apply (V : (threefold φ).Opens)
    (δ : (CycleQ2HodgeEulerTangentSheaf.tangent (toBase φ)).val.obj (op V)) :
    (volumeIso φ hg).hom.val.app (op V) δ =
      contractSection (N φ) V δ ((form (N φ) 3).val.map (homOfLE (le_top : V ≤ ⊤)).op
        (CycleQ2HodgeEulerVolume.omega φ hg)) :=
  gluedIso_apply _ _ _ _ _ _ _ _

end CycleQ2HodgeVolumeContraction
end

#print axioms CycleQ2HodgeVolumeContraction.volumeIso_apply
