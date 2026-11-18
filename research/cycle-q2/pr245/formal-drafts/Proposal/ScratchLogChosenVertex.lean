import Proposal.ScratchLogChosenCofactor
import Proposal.ScratchLogChosenRestrictions

/-!
# Evaluation of the chosen cone residue in the native function field

Use the universal sextic, the zeroth weight-one chart and its first
homogeneous partial. The regular three-form obtained from the cone
cochain agrees with the prescribed density in the generic field.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LogChosenVertex

open AlgebraicGeometry MvPolynomial
open CycleQ2WeightedConeUniversal (Base coefficients topForm generic_normal)
open CycleQ2WeightedGenericPointMap (genericPoint chosen)
open CycleQ2GeometricHodgeThreefold (equation toBase)
open CycleQ2WeightedChosenResidue (A V coordinate coefficient form)
open CycleQ2WeightedResidueAtlas (U normalIndex)
open CycleQ2WeightedChartShear (coordWedge)
open CycleQ2WeightedGradientSectionUnits (patch_le_coordinate derivative_section_unit)
open CycleQ2WeightedCechPresentations (denominators denominators_map_units)
open CycleQ2WeightedNativeOverlapSection (coordAt)
open CycleQ2WeightedConeChartRestrictions (coord)
open CycleQ2WeightedRepresentedForms (projected)
open CycleQ2WeightedProjectedSections (sectionEval)
open CycleQ2ConeSimplexCochain (Regular)
open CycleQ2LogChosenCofactor (projected_vertex spatial)
open CycleQ2LogChosenRestrictions (read read_pivot read_spatial read_coefficient)
open CycleQ2HodgeEulerContractionRestriction (pull)
open CycleQ2LogarithmicPullback (Forms exactWedge)
open scoped CycleQ2WeightedConeUniversal

local instance : Algebra Base A := CycleQ2.Cech.Sections.algebra (toBase coefficients) V
private abbrev index : Fin 1 → Fin 5 := fun _ => 1
private abbrev T := CycleQ2ConeSimplexCochain.support index
private abbrev h : (1 : Fin 5) ∈ T := CycleQ2ConeSimplexCochain.mem_support index 0
local notation "G" => equation coefficients
local notation "M" => denominators G (T : Set (Fin 5))
local notation "cx" => coord coefficients M
local notation "xp" => coordAt coefficients 0 V (patch_le_coordinate coefficients chosen)

private theorem only_one {i : Fin 5} (hi : i ∈ T) : i=1 := by
  obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hi
  rfl

private theorem active : Regular coefficients T := by
  intro i hi hzero
  have e := only_one hi
  subst i
  apply generic_normal
  change _ (pderiv (1 : Fin 5) G) = 0
  rw [hzero,map_zero]

private theorem units : ∀ m : M, IsUnit (aeval xp (m : MvPolynomial (Fin 5) Base)) := by
  refine denominators_map_units G (T : Set (Fin 5)) (aeval xp).toRingHom ?_
  intro j hj
  have e := only_one hj
  subst j
  exact derivative_section_unit coefficients chosen 0 V (le_refl V) (patch_le_coordinate _ _)

/-- The actual projectively normalized vertex in regular sections on the selected open. -/
def source : Forms Base A 3 :=
  -(pull (read T units) 3 (projected coefficients M 2
    (CycleQ2ConeSimplexCochain.vertex coefficients index)))

theorem source_eq_form : source = form := by
  change -(pull (read T units) 3 (projected coefficients M 2
    (CycleQ2ConeSimplexCochain.rV coefficients T h h))) = _
  rw [projected_vertex T h coefficients (read T units) active (read_pivot T units)]
  rw [show (read T units) _ = coefficient from read_coefficient T units h active]
  have hs : (fun j : Fin 3 => read T units (cx j.succ.succ)) = coordinate :=
    funext (read_spatial T units)
  change coefficient • exactWedge (k:=Base) 3 (fun j : Fin 3 => read T units (cx j.succ.succ)) =
    coefficient • exactWedge (k:=Base) 3 coordinate
  rw [hs]

/-- The sought three-form in the literal function field is the generic-point
image of the genuine projected, normalized cone vertex. -/
theorem generic_source : pull genericPoint 3 source = topForm := by
  rw [source_eq_form]
  exact CycleQ2WeightedChosenResidue.genericPoint_form

end CycleQ2LogChosenVertex
end

#print axioms CycleQ2LogChosenVertex.source_eq_form
#print axioms CycleQ2LogChosenVertex.generic_source
