import Proposal.GeometricLiteralThreefoldResidueGluing
import Proposal.GeometricLiteralThreefoldOverlapAtlas

/-!
# The residue volume of the original projective sextic threefold

Each oriented affine residue defines a section of the exterior cube of the
Kähler differential sheaf. The scheme maps from the affine chart intersections
identify their restrictions. Descent over the four projective coordinate opens
then gives a unique global section with the prescribed residues.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldCanonicalVolume

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricPrincipalChartSections
  CycleQ2ChartExteriorBinding CycleQ2ExteriorSectionNaturality
  CycleQ2LiteralAmbientSmooth CycleQ2LiteralAmbientCharts CycleQ2LiteralAbelJacobiContraction
  CycleQ2LiteralThreefoldResidueCoordinates CycleQ2LiteralThreefoldChartVolume
  CycleQ2LiteralThreefoldResidueChartMaps CycleQ2LiteralThreefoldResidueGluing
  CycleQ2LiteralThreefoldOverlapAtlas

attribute [local instance] CycleQ2LiteralThreefoldResidueChartMaps.sourceFixedAlgebra
  CycleQ2LiteralThreefoldResidueChartMaps.sourceFixedTower

abbrev X := IncidenceFiber 57
abbrev structural := incidenceFiberToComplex 57
abbrev coeff := schemeCoefficient structural
abbrev oneForms := differentialSheaf X.sheaf coeff
abbrev threeForms := exteriorSheaf X.sheaf oneForms.val 3

theorem chartOverComplex (i : Fin 4) :
    (fixedChart i).symm.inv ≫ (fixedOpen i).ι ≫ structural =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (T i))) := by
  simpa only [Iso.symm_inv, chartInclusion, Category.assoc, structural] using
    chartInclusion_overComplex i

/-- The section obtained from the oriented three-form on the entire affine chart. -/
def chartVolumeSection (i : Fin 4) : threeForms.val.obj (op (fixedOpen i)) :=
  chartExteriorSheafSection (fixedChart i).symm structural (chartOverComplex i)
    3 (Over.mk (𝟙 (fixedOpen i))) ((-1 : T i)^i.val • chartVolume i)

section OnIntersection

variable (i : Fin 4) (k : Fin 3)

private abbrev W := fixedOpen i ⊓ fixedOpen (i.succAbove k)

private abbrev sourceMap := IsScalarTower.toAlgHom ℂ (T i) (FixedOverlap i k)

variable (e : (W i k).toScheme ≅ Spec (CommRingCat.of (FixedOverlap i k)))
  (h₁ : e.inv ≫ (W i k).ι = Spec.map (CommRingCat.ofHom (sourceMap i k).toRingHom) ≫ chartInclusion i)
  (h₂ : e.inv ≫ (W i k).ι = Spec.map (CommRingCat.ofHom (fixedTargetMap i k).toRingHom) ≫
    chartInclusion (i.succAbove k))

include h₁ in
private theorem overlapOverComplex :
    e.inv ≫ (W i k).ι ≫ structural = Spec.map (CommRingCat.ofHom (algebraMap ℂ (FixedOverlap i k))) := by
  rw [← Category.assoc, h₁, Category.assoc]
  change _ ≫ chartInclusion i ≫ incidenceFiberToComplex 57 = _
  rw [chartInclusion_overComplex, ← Spec.map_comp]
  apply congrArg Spec.map
  apply CommRingCat.hom_ext
  apply RingHom.ext
  exact (sourceMap i k).commutes

include h₁ in
private theorem chartVolumeSection_restrict (j : Fin 4) (h : W i k ≤ fixedOpen j)
    (φ : T j →ₐ[ℂ] FixedOverlap i k)
    (hφ : e.inv ≫ (W i k).ι = Spec.map (CommRingCat.ofHom φ.toRingHom) ≫ chartInclusion j) :
    threeForms.val.map (homOfLE h).op (chartVolumeSection j) =
      chartExteriorSheafSection e structural (overlapOverComplex i k e h₁)
        3 (Over.mk (𝟙 (W i k))) (exteriorDifferentialMap φ 3 ((-1 : T j)^j.val • chartVolume j)) := by
  calc
    _ = chartExteriorSheafSection (fixedChart j).symm structural (chartOverComplex j)
        3 (Over.mk (homOfLE h)) _ :=
      chartExteriorSheafSection_restrict _ _ _
        (Over.homMk (homOfLE h) : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 (fixedOpen j))) 3 _
    _ = _ := (chartExteriorSheafSection_differentialMap (fixedChart j).symm e h structural
      (chartOverComplex j) (overlapOverComplex i k e h₁) φ hφ (Over.mk (𝟙 (W i k))) 3 _).symm

include h₁ h₂ in
private theorem chartVolumeSection_agreement :
    threeForms.val.map (homOfLE (show W i k ≤ fixedOpen i from inf_le_left)).op (chartVolumeSection i) =
    threeForms.val.map (homOfLE (show W i k ≤ fixedOpen (i.succAbove k) from inf_le_right)).op
      (chartVolumeSection (i.succAbove k)) := by
  rw [chartVolumeSection_restrict i k e h₁ i inf_le_left (sourceMap i k) h₁,
    chartVolumeSection_restrict i k e h₁ (i.succAbove k) inf_le_right (fixedTargetMap i k) h₂]
  apply congrArg (chartExteriorSheafSection _ _ _ _ _)
  simpa only [map_smulₛₗ, RingHom.map_pow, map_neg, map_one] using
    (fixedChartVolume_overlap i k).symm

end OnIntersection

private def threeFormsAdd : TopCat.Sheaf AddCommGrpCat X := (SheafOfModules.toSheaf (ringSheaf X.sheaf)).obj threeForms

private theorem volume_compatible :
    TopCat.Presheaf.IsCompatible threeFormsAdd.obj fixedOpen chartVolumeSection := by
  intro i j
  by_cases h : j = i
  · subst j
    rfl
  · obtain ⟨k, rfl⟩ := Fin.exists_succAbove_eq h
    exact chartVolumeSection_agreement i k (overlapIso i k).symm
      (overlapIso_hom_ι i k) (overlapIso_hom_ι_target i k)

/-- The actual chart sections glue uniquely in the exterior cube sheaf of the fixed threefold. -/
theorem existsUnique_volume :
    ∃! v : threeForms.val.obj (op ⊤), ∀ i : Fin 4,
      threeForms.val.map (homOfLE (le_top : fixedOpen i ≤ ⊤)).op v = chartVolumeSection i := by
  obtain ⟨σ,hσ,hu⟩ := threeFormsAdd.existsUnique_gluing' fixedOpen ⊤
    (fun i => homOfLE (le_top : fixedOpen i ≤ ⊤)) fixedOpen_cover.ge chartVolumeSection volume_compatible
  exact ⟨σ,hσ,hu⟩

/-- The global volume of the literal fixed weighted threefold. -/
def volume : threeForms.val.obj (op ⊤) := Classical.choose existsUnique_volume

theorem volume_restrict (i : Fin 4) :
    threeForms.val.map (homOfLE (le_top : fixedOpen i ≤ ⊤)).op volume = chartVolumeSection i :=
  (Classical.choose_spec existsUnique_volume).1 i

/-- Restriction to any smaller open is the section induced by the same chart form. -/
theorem volume_restrict_subopen (i : Fin 4) (U : X.Opens) (h : U ≤ fixedOpen i) :
    threeForms.val.map (homOfLE (le_top : U ≤ ⊤)).op volume =
      chartExteriorSheafSection (fixedChart i).symm structural (chartOverComplex i)
        3 (Over.mk (homOfLE h)) ((-1 : T i)^i.val • chartVolume i) := by
  exact (threeForms.val.map_comp_apply
    (homOfLE (le_top : fixedOpen i ≤ ⊤)).op (homOfLE h).op volume).trans
    ((congrArg (fun s => threeForms.val.map (homOfLE h).op s) (volume_restrict i)).trans
      (chartExteriorSheafSection_restrict _ _ _
        (Over.homMk (homOfLE h) : Over.mk (homOfLE h) ⟶ Over.mk (𝟙 (fixedOpen i))) 3 _))

end CycleQ2LiteralThreefoldCanonicalVolume
end

#print axioms CycleQ2LiteralThreefoldCanonicalVolume.existsUnique_volume
#print axioms CycleQ2LiteralThreefoldCanonicalVolume.volume_restrict_subopen
