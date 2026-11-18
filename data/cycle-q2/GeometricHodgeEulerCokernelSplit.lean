import Proposal.GeometricSeedSectionSheafLimits
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-! A local retraction of a sheaf inclusion splits the actual cokernel
after restriction. The two identities retain the original quotient map
and exhibit its section explicitly.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2HodgeEulerCokernelSplit
open CategoryTheory Limits
variable {C D : Type*} [Category* C] [Category* D] [Preadditive C] [Preadditive D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] {M N : C} (a : M ⟶ N) [HasCokernel a]
  [HasCokernel (F.map a)] [PreservesColimit (parallelPair a 0) F]
  (r : F.obj N ⟶ F.obj M) (hr : F.map a ≫ r = 𝟙 _)

def lift : F.obj (cokernel a) ⟶ F.obj N :=
  (PreservesCokernel.iso F a).hom ≫ cokernel.desc (F.map a) (𝟙 _ - r ≫ F.map a)
    (by rw [Preadditive.comp_sub, Category.comp_id, ← Category.assoc, hr, Category.id_comp, sub_self])

theorem project_lift : F.map (cokernel.π a) ≫ lift F a r hr = 𝟙 _ - r ≫ F.map a := by
  rw [lift, PreservesCokernel.π_iso_hom_assoc, cokernel.π_desc]

theorem lift_project : lift F a r hr ≫ F.map (cokernel.π a) = 𝟙 _ := by
  apply (cancel_epi ((PreservesCokernel.iso F a).inv)).mp
  apply (cancel_epi (cokernel.π (F.map a))).mp
  have hπ : cokernel.π (F.map a) ≫ (PreservesCokernel.iso F a).inv = F.map (cokernel.π a) := by
    rw [← PreservesCokernel.π_iso_hom F a, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  rw [← Category.assoc, ← Category.assoc, hπ, ← Category.assoc, project_lift,
    Preadditive.sub_comp, Category.id_comp, Category.assoc, ← F.map_comp, cokernel.condition,
    F.map_zero, comp_zero, sub_zero, Category.comp_id]
  exact hπ.symm

end CycleQ2HodgeEulerCokernelSplit
end
#print axioms CycleQ2HodgeEulerCokernelSplit.lift_project
