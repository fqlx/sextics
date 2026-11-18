import Proposal.GeometricHodgeCyclicSheafResidue
import Proposal.GeometricHodgeEulerVolume

/-! # The character of the global projective volume

The sixteen gradient opens cover the full moving fiber at every good
parameter. Comparing the pullback of the global section on these opens
gives its character in the global exterior-cube sheaf.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeCyclicVolume
open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  CycleQ2GenericSexticGradient CycleQ2GeometricHodgeThreefold CycleQ2GeometricModuleLocalIso
  CycleQ2GeometricDifferentialSheaf CycleQ2HodgeEulerVolume CycleQ2HodgeCyclicSheafResidue
  CycleQ2HodgeCyclicAction CycleQ2GeometricTwistedDifferential

variable (φ : CoeffRing →+* ℂ) (hg : IsUnit (φ goodParameter)) (z : ℂ) (hz : z^3=1)

theorem omega_pull :
    (pulling φ z hz 3).val.app (op ⊤) (omega φ hg) =
      coefficientOn (threefold φ).sheaf (κ φ) ⊤ (z^2) • omega φ hg := by
  let M := threeForms φ
  let g := (action φ z hz).hom
  let L := pulling φ z hz 3
  apply (addSheaf M).eq_of_locally_eq' (fun a : Fin 4 × Fin 4 => U φ a.1 a.2) ⊤
    (fun _ => homOfLE le_top) (CycleQ2HodgeGradientAtlas.cover φ hg).ge
  rintro ⟨i,j⟩
  let W := U φ i j
  let hW : W ≤ (⊤ : (threefold φ).Opens) := le_top
  let hw := (stable φ z hz i j).ge
  let resW := M.val.map (homOfLE hW).op
  have hvol : resW (omega φ hg) = chartForm φ i j 3
      (CycleQ2HodgeEulerContractionCharts.projectiveResidue (CycleQ2HodgeEuler.F φ i) i j) :=
    omega_on_gradient φ hg i j (CycleQ2HodgeGradientAtlas.U_le φ i j) (atlas φ i j) (overBase φ i j)
      (CycleQ2HodgeGradientAtlas.atlas_inv_ι φ i j)
  have hn := PresheafOfModules.naturality_apply L.val (homOfLE hW).op (omega φ hg)
  have hres : resW (L.val.app (op ⊤) (omega φ hg)) =
      M.val.map (homOfLE hw).op (L.val.app (op W) (resW (omega φ hg))) := by
    change M.val.map (homOfLE hW).op _ = _
    calc
      _ = M.val.map (homOfLE hw).op (M.val.map ((Opens.map g.base).map (homOfLE hW)).op
          (L.val.app (op ⊤) (omega φ hg))) := M.val.map_comp_apply _ _ _
      _ = _ := congrArg (M.val.map (homOfLE hw).op) hn.symm
  change resW (L.val.app (op ⊤) (omega φ hg)) =
    resW (coefficientOn (threefold φ).sheaf (κ φ) ⊤ (z^2) • omega φ hg)
  rw [hres, hvol, CycleQ2HodgeCyclicSheafResidue.residue]
  change _ = M.val.map (homOfLE hW).op (_ • _)
  rw [M.val.map_smul]
  exact congrArg₂ (· • ·) (coefficientOn_restrict _ _ hW (z^2)).symm hvol.symm

end CycleQ2HodgeCyclicVolume
end

#print axioms CycleQ2HodgeCyclicVolume.omega_pull
