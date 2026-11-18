import Proposal.GeometricHodgeEulerVolumeOverlap
import Proposal.GeometricHodgeEulerOverlapBinding
import Proposal.GeometricHodgeThreefoldProper

/-!
# The global oriented volume of every good moving sextic fiber

The regular residues of the full coordinate charts agree through both
maps of their native projective intersections. Descent gives a unique
global section of the genuine exterior cube of the cotangent sheaf.
On every smooth gradient chart it is the normalized Poincaré residue.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeEulerVolume

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricPrincipalChartSections
  CycleQ2ChartExteriorBinding CycleQ2ExteriorSectionNaturality
  CycleQ2GenericSexticGradient CycleQ2GeometricHodgeThreefold
  CycleQ2HodgeEulerChartBinding CycleQ2HodgeEulerOverlapBinding
  CycleQ2HodgeEulerVolumeChart CycleQ2HodgeEulerContractionCharts
open CycleQ2GeometricDifferentialChartTransport (chartTop)
open CycleQ2HodgeEuler (F chart overlap overlapMap)
open CycleQ2HodgeEulerContractionNative (sourceMap)
open scoped KaehlerDifferential

variable (φ : CoeffRing →+* ℂ) (hg : IsUnit (φ goodParameter))

include hg in
theorem gradient_unit : IsUnit (φ gradientOpen) := by
  rw [goodParameter, map_mul, IsUnit.mul_iff] at hg
  exact hg.1

abbrev threeForms := exteriorSheaf (threefold φ).sheaf
  (differentialSheaf (threefold φ).sheaf (schemeCoefficient (toBase φ))).val 3

def chartSection (i : Fin 4) : (threeForms φ).val.obj (op (coordinateOpen φ i)) :=
  chartExteriorSheafSection (affineChart φ i) (toBase φ) (affineChart_overBase φ i)
    3 (chartTop _) (orientedVolume φ (gradient_unit φ hg) i)

private theorem restrict_chart {W : (threefold φ).Opens} (i : Fin 4) (hW : W ≤ coordinateOpen φ i)
    {A : Type} [CommRing A] [Algebra ℂ A] (e : W.toScheme ≅ Spec (CommRingCat.of A))
    (he : e.inv ≫ W.ι ≫ toBase φ = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
    (g : chart φ i →ₐ[ℂ] A)
    (hmap : e.inv ≫ W.ι = Spec.map (CommRingCat.ofHom g.toRingHom) ≫ (affineChart φ i).inv ≫ (coordinateOpen φ i).ι) :
    (threeForms φ).val.map (homOfLE hW).op (chartSection φ hg i) =
      chartExteriorSheafSection e (toBase φ) he 3 (chartTop W)
        (CycleQ2HodgeEulerContractionRestriction.pull g 3 (orientedVolume φ (gradient_unit φ hg) i)) := by
  rw [← exteriorDifferentialMap_eq_pull]
  calc
    _ = chartExteriorSheafSection (affineChart φ i) (toBase φ) (affineChart_overBase φ i)
        3 (Over.mk (homOfLE hW)) _ :=
      chartExteriorSheafSection_restrict _ _ _
        (Over.homMk (homOfLE hW) : Over.mk (homOfLE hW) ⟶ Over.mk (𝟙 (coordinateOpen φ i))) 3 _
    _ = _ := (chartExteriorSheafSection_differentialMap (affineChart φ i) e hW (toBase φ)
      (affineChart_overBase φ i) he g hmap (chartTop W) 3 _).symm

private theorem section_agrees (i : Fin 4) (a : Fin 3) :
    (threeForms φ).val.map (homOfLE (show intersection φ i (i.succAbove a) ≤ coordinateOpen φ i from inf_le_left)).op
        (chartSection φ hg i) =
      (threeForms φ).val.map (homOfLE (show intersection φ i (i.succAbove a) ≤ coordinateOpen φ (i.succAbove a) from inf_le_right)).op
        (chartSection φ hg (i.succAbove a)) := by
  let k := i.succAbove a
  rw [restrict_chart φ hg i inf_le_left (overlapChart φ i k) (overlapChart_overBase φ i k)
    (sourceMap φ i a) (overlapChart_to_first φ i k)]
  rw [restrict_chart φ hg k inf_le_right (overlapChart φ i k) (overlapChart_overBase φ i k)
    (overlapMap φ i k) (overlapChart_to_second φ i k)]
  exact congrArg _ (CycleQ2HodgeEulerVolumeOverlap.overlap_volume φ i a (gradient_unit φ hg)).symm

private def additive := (SheafOfModules.toSheaf (ringSheaf (threefold φ).sheaf)).obj (threeForms φ)

private theorem section_compatible :
    TopCat.Presheaf.IsCompatible (additive φ).obj (coordinateOpen φ) (chartSection φ hg) := by
  intro i j
  by_cases h : j = i
  · subst j; rfl
  · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq h
    exact section_agrees φ hg i a

theorem existsUnique_omega :
    ∃! ω : (threeForms φ).val.obj (op ⊤), ∀ i : Fin 4,
      (threeForms φ).val.map (homOfLE (le_top : coordinateOpen φ i ≤ ⊤)).op ω = chartSection φ hg i := by
  obtain ⟨s,hs,hu⟩ := (additive φ).existsUnique_gluing' (coordinateOpen φ) ⊤
    (fun i => homOfLE (le_top : coordinateOpen φ i ≤ ⊤)) (coordinateOpens_cover_of_good φ hg).ge
    (chartSection φ hg) (section_compatible φ hg)
  exact ⟨s,hs,hu⟩

def omega : (threeForms φ).val.obj (op ⊤) := (existsUnique_omega φ hg).choose

theorem omega_restrict (i : Fin 4) :
    (threeForms φ).val.map (homOfLE (le_top : coordinateOpen φ i ≤ ⊤)).op (omega φ hg) = chartSection φ hg i :=
  ((existsUnique_omega φ hg).choose_spec).1 i

theorem omega_restrict_subopen {W : (threefold φ).Opens} (i : Fin 4) (hW : W ≤ coordinateOpen φ i) :
    (threeForms φ).val.map (homOfLE (le_top : W ≤ ⊤)).op (omega φ hg) =
      chartExteriorSheafSection (affineChart φ i) (toBase φ) (affineChart_overBase φ i)
        3 (Over.mk (homOfLE hW)) (orientedVolume φ (gradient_unit φ hg) i) := by
  exact ((threeForms φ).val.map_comp_apply
    (homOfLE (le_top : coordinateOpen φ i ≤ ⊤)).op (homOfLE hW).op (omega φ hg)).trans
    ((congrArg (fun s => (threeForms φ).val.map (homOfLE hW).op s) (omega_restrict φ hg i)).trans
      (chartExteriorSheafSection_restrict _ _ _
        (Over.homMk (homOfLE hW) : Over.mk (homOfLE hW) ⟶ Over.mk (𝟙 (coordinateOpen φ i))) 3 _))

/-- Restriction to any identified gradient open is the genuine chart section of the
signed Poincaré residue, including its inverse partial coefficient. -/
theorem omega_on_gradient {W : (threefold φ).Opens} (i j : Fin 4) (hW : W ≤ coordinateOpen φ i)
    (e : W.toScheme ≅ Spec (CommRingCat.of (Patch (F φ i) j)))
    (he : e.inv ≫ W.ι ≫ toBase φ = Spec.map (CommRingCat.ofHom (algebraMap ℂ (Patch (F φ i) j))))
    (hmap : e.inv ≫ W.ι = Spec.map (CommRingCat.ofHom (patchMap (F φ i) j).toRingHom) ≫
      (affineChart φ i).inv ≫ (coordinateOpen φ i).ι) :
    (threeForms φ).val.map (homOfLE (le_top : W ≤ ⊤)).op (omega φ hg) =
      chartExteriorSheafSection e (toBase φ) he 3 (chartTop W) (projectiveResidue (F φ i) i j) := by
  calc
    _ = (threeForms φ).val.map (homOfLE hW).op ((threeForms φ).val.map (homOfLE (le_top : coordinateOpen φ i ≤ ⊤)).op (omega φ hg)) :=
      (threeForms φ).val.map_comp_apply _ _ _
    _ = _ := by
      rw [omega_restrict, restrict_chart φ hg i hW e he (patchMap (F φ i) j) hmap, pull_orientedVolume]

end CycleQ2HodgeEulerVolume
end

#print axioms CycleQ2HodgeEulerVolume.omega_restrict
#print axioms CycleQ2HodgeEulerVolume.omega_on_gradient
