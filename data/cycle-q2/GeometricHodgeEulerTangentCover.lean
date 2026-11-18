import Proposal.GeometricChartTangentMaps
import Proposal.GeometricHodgeThreefoldProper
import Proposal.GeometricHodgeEulerChartBinding
import Mathlib.Topology.Sheaves.SheafCondition.Sites
import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification

/-! Glue local module morphisms by the sheaf property of the genuine
internal Hom. Principal affine subopens of the four normalized charts
form a basis for detecting isomorphisms on the original threefold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerTangentCover

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal

section Glue
variable {X : Scheme.{0}} (M N : X.Modules) {I : Type} (U : I → X.Opens)
  (hu : (⨆ i, U i) = ⊤) (L : ∀ i, LocalLinearHom X.sheaf M N (U i))
  (hc : ∀ i j, restrictLocalLinearHom X.sheaf M N
      (homOfLE (show U i ⊓ U j ≤ U i from inf_le_left)).op (L i) =
    restrictLocalLinearHom X.sheaf M N
      (homOfLE (show U i ⊓ U j ≤ U j from inf_le_right)).op (L j))

include hu hc in
private theorem exists_glue : ∃! g : LocalLinearHom X.sheaf M N ⊤,
    ∀ i, restrictLocalLinearHom X.sheaf M N (homOfLE (show U i ≤ ⊤ from le_top)).op g = L i := by
  let S : TopCat.Sheaf AddCommGrpCat X :=
    (SheafOfModules.toSheaf X.ringCatSheaf).obj (moduleHomSheaf X.sheaf M N)
  let sf (i : I) : S.obj.obj (op (U i)) := L i
  apply S.existsUnique_gluing' U ⊤ (fun _ => homOfLE le_top) hu.ge sf
  intro i j
  exact hc i j

def glue : M ⟶ N :=
  localLinearHomTopEquiv X.sheaf M N (Classical.choose (exists_glue M N U hu L hc).exists)

theorem glue_apply (i : I) (V : X.Opens) (hi : V ≤ U i) (s : Γ(M,V)) :
    (glue M N U hu L hc).app V s = (L i).val.app (op (Over.mk (homOfLE hi))) s := by
  let g := Classical.choose (exists_glue M N U hu L hc).exists
  have hg := Classical.choose_spec (exists_glue M N U hu L hc).exists i
  change g.val.app (op (Over.mk (homOfLE (show V ≤ ⊤ from le_top)))) s = _
  rw [← hg]
  rfl

end Glue

open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R)

abbrev chartIncl (i : Fin 4) := (affineChart φ i).inv ≫ (coordinateOpen φ i).ι

abbrev basic (w : (i : Fin 4) × chart φ i) : (threefold φ).Opens :=
  chartIncl φ w.1 ''ᵁ PrimeSpectrum.basicOpen w.2

theorem basis (hv : IsUnit (φ vertexCoefficient)) : Opens.IsBasis (Set.range (basic φ)) := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro W x hx
  have h : x ∈ ⨆ i : Fin 4, coordinateOpen φ i := by rw [coordinateOpens_cover φ hv]; trivial
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp h
  have hr : (chartIncl φ i).opensRange = coordinateOpen φ i := by
    rw [Scheme.Hom.opensRange_comp_of_isIso, Scheme.Opens.opensRange_ι]
  rw [← hr] at hi
  obtain ⟨y, rfl⟩ : x ∈ Set.range (chartIncl φ i) := hi
  have hy : y ∈ chartIncl φ i ⁻¹ᵁ W := hx
  obtain ⟨_, ⟨_, ⟨z, rfl⟩, rfl⟩, hz, hzW⟩ := PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
    hy (chartIncl φ i ⁻¹ᵁ W).isOpen
  exact ⟨_, ⟨⟨i,z⟩, rfl⟩, ⟨y,hz,rfl⟩, fun _ ⟨b,hb,he⟩ => he ▸ hzW hb⟩

private theorem reflects_additive {Y : Scheme.{0}} :
    (SheafOfModules.toSheaf.{0} Y.ringCatSheaf).ReflectsIsomorphisms := by
  let F := SheafOfModules.toSheaf.{0} Y.ringCatSheaf
  let G := sheafToPresheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{0}
  let : (F ⋙ G).ReflectsIsomorphisms :=
    inferInstanceAs (SheafOfModules.forget.{0} Y.ringCatSheaf ⋙
      PresheafOfModules.toPresheaf _).ReflectsIsomorphisms
  exact reflectsIsomorphisms_of_comp F G

theorem iso_of_basis {M N : (threefold φ).Modules} (m : M ⟶ N) (hv : IsUnit (φ vertexCoefficient))
    (hm : ∀ w, Function.Bijective (m.app (basic φ w))) : IsIso m := by
  let F := SheafOfModules.toSheaf (threefold φ).ringCatSheaf
  have : IsIso (F.map m) := TopCat.Sheaf.isIso_iff_isIso_basis (φ := F.map m) (basis φ hv)
    (fun w => (ConcreteCategory.isIso_iff_bijective _).mpr (hm w))
  let : F.ReflectsIsomorphisms := reflects_additive
  exact isIso_of_reflects_iso m F

end CycleQ2HodgeEulerTangentCover
end

#print axioms CycleQ2HodgeEulerTangentCover.glue_apply
#print axioms CycleQ2HodgeEulerTangentCover.iso_of_basis
