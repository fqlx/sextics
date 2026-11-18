import Proposal.GeometricLiteralNegativeTwistDescent
import Mathlib.Topology.Sheaves.LocallySurjective

/-!
# Finite Čech representatives in degree one on a compact space

Local lifts of a section of the first injective quotient give a Čech
cocycle for the corresponding derived class. Compactness gives a finite
cover; the cover may depend on the class. This makes functorial identities
on finite Čech representatives available on the entire cohomology group.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2HodgeCompactOneCocycles

open CategoryTheory CategoryTheory.Abelian TopologicalSpace Opposite
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2FiniteCechHOne

open CycleQ2CechTwoToDerived (presentation presentation_shortExact sectionExtZero app app_res
  app_injective sections_exact)

variable {X : TopCat.{0}} [CompactSpace X]
local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _

theorem representative (F : AbSheaf X) (x : F.H' 1 ⊤) :
    ∃ (t : Finset X) (U : t → Opens X) (hcover : (⨆ i, U i) = ⊤)
      (c : One F U) (hc : IsOneCocycle F U c), cechOneClass U hcover c hc = x := by
  classical
  let S := presentation F
  have hS : S.ShortExact := presentation_shortExact F
  obtain ⟨z, hz⟩ := Ext.covariant_sequence_exact₁ (freeOpen (⊤ : Opens X)) hS x
    (Ext.eq_zero_of_injective _) rfl
  obtain ⟨φ,rfl⟩ := (Ext.mk₀_bijective _ _).surjective z
  let q := freeOpenSections S.X₃ ⊤ φ
  have hs := (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat S.g).mpr hS.epi_g
  have hl := (TopCat.Presheaf.isLocallySurjective_iff S.g.hom).mp hs ⊤ q
  choose V hV b hb using fun y : X => hl y (show y ∈ (⊤ : Opens X) from trivial)
  choose p hp using b
  have hv : Set.univ ⊆ ⋃ y, (V y : Set X) := fun y _ => Set.mem_iUnion.mpr ⟨y,hb y⟩
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (V y : Set X)) (fun y => (V y).isOpen) hv
  let U : t → Opens X := fun i => V i.val
  have hcover : (⨆ i, U i) = ⊤ := by
    apply top_unique
    intro y _
    obtain ⟨i,hi⟩ := Set.mem_iUnion.mp (ht (Set.mem_univ y))
    obtain ⟨hit,hy⟩ := Set.mem_iUnion.mp hi
    exact Opens.mem_iSup.mpr ⟨⟨i,hit⟩,hy⟩
  have hlocal (i : t) : app S.g (U i) (p i.val) = res S.X₃ le_top q := hp i.val
  have diff (i j : t) : app S.g (U i ⊓ U j)
      (res S.X₂ inf_le_right (p j.val) - res S.X₂ inf_le_left (p i.val)) = 0 := by
    rw [map_sub, app_res, app_res, hlocal, hlocal, res_comp, res_comp, sub_self]
  choose c hc using fun i j => sections_exact hS (U i ⊓ U j) _ (diff i j)
  have edge (i j : t) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
      app S.f W (edgeValue F U c i j W hi hj) =
        res S.X₂ hj (p j.val) - res S.X₂ hi (p i.val) := by
    rw [edgeValue, app_res, hc, map_sub]
    exact congrArg₂ (· - ·)
      (res_comp S.X₂ (inf_le_right : U i ⊓ U j ≤ U j) (le_inf hi hj) (p j.val))
      (res_comp S.X₂ (inf_le_left : U i ⊓ U j ≤ U i) (le_inf hi hj) (p i.val))
  have hc' : IsOneCocycle F U c := by
    intro i j k W hi hj hk
    change edgeValue F U c i k W hi hk = edgeValue F U c i j W hi hj + edgeValue F U c j k W hj hk
    apply app_injective S.f W
    rw [map_add, edge, edge, edge]
    abel
  let d : OneDescent U c := {
    primitive := fun i => p i.val
    differential := fun i j W hi hj => (edge i j W hi hj).symm
    globalSection := q
    global_restriction := funext (fun i => (hlocal i).symm) }
  refine ⟨t,U,hcover,c,hc',(cechOneClass_eq_descentClass U hcover c hc' d).trans ?_⟩
  change (sectionExtZero ⊤ q).comp hS.extClass rfl = x
  simpa only [q, sectionExtZero, AddEquiv.symm_apply_apply] using hz

end CycleQ2HodgeCompactOneCocycles
end
#print axioms CycleQ2HodgeCompactOneCocycles.representative
