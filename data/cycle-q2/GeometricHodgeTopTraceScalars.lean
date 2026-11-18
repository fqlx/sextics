import Proposal.GeometricHodgeTwistAnchorBase
import Proposal.GeometricHodgeTopCech
import Proposal.GeometricAffineChartSections

import Proposal.GeometricHodgeTwistTorusChart
import Proposal.GeometricHodgeDerivedTopTrace
import Proposal.GeometricFourOpenHThreeNaturality
import Proposal.GeometricSheafCohomologyScalar

/-!
# Complex linearity of the top trace on the weighted threefold

The representative of a scalar in top cohomology is its multiple of
the all-negative Laurent monomial. Multiplication by a scalar commutes
with the three Mayer–Vietoris connecting maps carrying that section
to top cohomology.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 900000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeTopTraceScalars

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricHodgeThreefold
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeTwistAnchor (torus torus_le commonCoefficient frameCoefficient)
open CycleQ2HodgeTwistMonomials (evaluate monomial)
open CycleQ2GeometricAffineChartSections (schemeCoefficient)
open CycleQ2GeometricDifferentialSheaf (coefficientOn)
open CycleQ2GeometricProjectiveCurve.Twisted (res res_comp)

private theorem restrict_top (X : Scheme.{0}) (U : X.Opens) :
    U.ι.appTop ≫ U.topIso.hom = X.presheaf.map (homOfLE (show U ≤ ⊤ from le_top)).op := by
  rw [Scheme.Opens.ι_appTop, Scheme.Opens.topIso_hom, ← Functor.map_comp]
  exact congrArg X.presheaf.map (Subsingleton.elim _ _)

private theorem chartScalar_map (φ : CoeffRing →+* ℂ) (i : Fin 4) :
    CommRingCat.ofHom (schemeCoefficient (toBase φ)) ≫ (threefold φ).presheaf.map
        (homOfLE (show coordinateOpen φ i ≤ ⊤ from le_top)).op =
      CommRingCat.ofHom (chartCoefficient φ i) ≫ Proj.awayToSection (grade φ) (coord φ i.castSucc) := by
  let U := coordinateOpen φ i
  let e := coordinateChart φ i
  have hb : e.inv ≫ U.ι ≫ toBase φ = Spec.map (CommRingCat.ofHom (chartCoefficient φ i)) := by
    change (Proj.basicOpenIsoSpec (grade φ) (coord φ i.castSucc) (weightOne_mem_grade φ i) (by decide)).inv ≫
      (Proj.basicOpen (grade φ) (coord φ i.castSucc)).ι ≫ toBase φ = _
    rw [Proj.basicOpenIsoSpec_inv_ι_assoc, toBase, Proj.awayι_toSpecZero_assoc, ← Spec.map_comp]
    rfl
  have h : U.ι ≫ toBase φ = e.hom ≫ Spec.map (CommRingCat.ofHom (chartCoefficient φ i)) :=
    (Iso.hom_inv_id_assoc e _).symm.trans (congrArg (fun k => e.hom ≫ k) hb)
  have he := congrArg (fun k : U.toScheme ⟶ Spec (CommRingCat.of ℂ) =>
    (Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ k.appTop ≫ U.topIso.hom) h
  simp only [Scheme.Hom.comp_appTop, U, e, coordinateChart, Proj.basicOpenIsoSpec_hom,
    Proj.basicOpenToSpec_app_top, Category.assoc, Scheme.ΓSpecIso_naturality_assoc,
    Iso.inv_hom_id_assoc, restrict_top] at he
  simpa only [schemeCoefficient, CommRingCat.ofHom_hom, Category.assoc,
    Proj.basicOpenIsoAway_hom, Iso.inv_hom_id, Category.comp_id, threefold, coordinateOpen] using he

theorem chartScalar (φ : CoeffRing →+* ℂ) (i : Fin 4) (c : ℂ) :
    coefficientOn (threefold φ).sheaf (schemeCoefficient (toBase φ)) (coordinateOpen φ i) c =
      (Proj.awayToSection (grade φ) (coord φ i.castSucc)) (chartCoefficient φ i c) := by
  exact congrArg (fun k : CommRingCat.of ℂ ⟶ Γ(threefold φ, coordinateOpen φ i) => k.hom c)
    (chartScalar_map φ i)

theorem torusScalar (φ : CoeffRing →+* ℂ) (c : ℂ) :
    coefficientOn (threefold φ).sheaf (schemeCoefficient (toBase φ)) (torus φ) c =
      commonCoefficient φ c := by
  have e := congrArg (res (threefold φ).sheaf (torus_le φ 0)) (chartScalar φ 0 c)
  change res _ _ (res _ _ (schemeCoefficient (toBase φ) c)) = commonCoefficient φ c at e
  rw [res_comp] at e
  exact e

theorem evaluate_representative {R : Type} [CommRing R] (φ : CoeffRing →+* R) (c : R) :
    evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0
        ((CycleQ2HodgeTopCech.representative c).val) =
      commonCoefficient φ c * monomial φ (torus φ) (torus_le φ) 0 2 (fun _ => -1) := by
  classical
  simp [evaluate, CycleQ2HodgeTopCech.representative, Fin.sum_univ_three]

open CycleQ2HodgeTwistTorusChart (structureChart structureLaurentSections)
open CycleQ2HodgeFourOpenStructureHThree (tripleConnecting)
open CycleQ2HodgeDerivedTopTrace (derivedTrace topCoordinates)
open CycleQ2FourOpenHThree (QuadOpen quad_eq_inf)
open CycleQ2GeometricProjectiveCurve.Twisted (resEquiv)
open CycleQ2GeometricSheafCohomologyScalar (cohomologyModule scalarEnd cohomologyScalar)
open CycleQ2GeometricModuleLocalIso (addSheaf)

private abbrev quad {R : Type} [CommRing R] (φ : CoeffRing →+* R) :=
  QuadOpen (coordinateOpen φ 0) (coordinateOpen φ 1) (coordinateOpen φ 2) (coordinateOpen φ 3)

private abbrev toTorus {R : Type} [CommRing R] (φ : CoeffRing →+* R) :=
  resEquiv (threefold φ).sheaf (quad_eq_inf (coordinateOpen φ)).ge (quad_eq_inf (coordinateOpen φ)).le

section Base
variable {R : Type} [CommRing R] [Nontrivial R] (φ : CoeffRing →+* R) (h : IsUnit (φ vertexCoefficient))

private theorem torus_evaluate (s : Γ(threefold φ, torus φ)) :
    evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0
      ((structureChart φ h).coordinates s) = s := by
  let W := torus φ
  let e := CycleQ2HodgeThreefoldTwist.chartFrame φ 0 0 W (torus_le φ 0)
  let p := e.symm s
  have hn := CycleQ2HodgeTwistAnchor.face_frame_evaluation φ 0 h Finset.univ (Finset.mem_univ _) 0 p
  change e (CycleQ2GeometricSheafLocalIso.res _ (show W ≤ W from le_rfl) p) = _ at hn
  rw [CycleQ2GeometricSheafLocalIso.res_self] at hn
  exact hn.symm.trans (e.apply_symm_apply s)

private abbrev repSection := CycleQ2HodgeDerivedTopTrace.representative (structureLaurentSections φ h)

/-- Actual section representing trace a, evaluated as one homogeneous fraction. -/
theorem representative_monomial (a : R) :
    toTorus φ (repSection φ h a) =
      commonCoefficient φ a * monomial φ (torus φ) (torus_le φ) 0 2 (fun _ => -1) := by
  let M := structureLaurentSections φ h
  calc
    _ = evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0
          ((topCoordinates M (repSection φ h a)).val) := (torus_evaluate φ h _).symm
    _ = _ := by
      rw [repSection, CycleQ2HodgeDerivedTopTrace.representative, AddEquiv.apply_symm_apply]
      exact evaluate_representative φ a
end Base

variable (φ : CoeffRing →+* ℂ) (h : IsUnit (φ vertexCoefficient))

private abbrev M := SheafOfModules.unit (threefold φ).ringCatSheaf
private abbrev coeff := schemeCoefficient (toBase φ)
private abbrev O := CycleQ2HodgeFourOpenStructureHThree.O φ

private theorem representative_smul (c a : ℂ) :
    (scalarEnd (threefold φ).sheaf (coeff φ) (M φ) c).hom.app (op (quad φ)) (repSection φ h a) =
      repSection φ h (c*a) := by
  apply (toTorus φ).injective
  change toTorus φ (coefficientOn (threefold φ).sheaf (coeff φ) (quad φ) c * repSection φ h a) = _
  rw [map_mul, representative_monomial, representative_monomial, map_mul, mul_assoc]
  congr 1
  exact (res_comp (threefold φ).sheaf (show quad φ ≤ ⊤ from le_top) (quad_eq_inf (coordinateOpen φ)).ge _).trans
    (torusScalar φ c)

local instance : HasExt.{1} (CycleQ2InjectiveCech.AbSheaf (show TopCat from threefold φ)) := HasExt.standard _
local instance : Module ℂ ((O φ).H' 3 ⊤) := cohomologyModule (threefold φ).sheaf (coeff φ) (M φ) 3 ⊤

private theorem generator_smul (c a : ℂ) :
    c • tripleConnecting φ h (repSection φ h a) = tripleConnecting φ h (repSection φ h (c*a)) := by
  exact (CycleQ2FourOpenHThreeNaturality.connectingAtTop_naturality
    (scalarEnd (threefold φ).sheaf (coeff φ) (M φ) c)
    (coordinateOpen φ 0) (coordinateOpen φ 1) (coordinateOpen φ 2) (coordinateOpen φ 3)
    (repSection φ h a) _).trans (congrArg (tripleConnecting φ h) (representative_smul φ h c a))

/-- The normalized Laurent trace is complex linear for the structure map of the actual threefold. -/
def structureTraceLinear : (O φ).H' 3 ⊤ ≃ₗ[ℂ] ℂ where
  toAddEquiv := derivedTrace φ h (structureLaurentSections φ h)
  map_smul' c x := by
    let E := derivedTrace φ h (structureLaurentSections φ h)
    obtain ⟨a, rfl⟩ := E.symm.surjective x
    change E (c • E.symm a) = c * E (E.symm a)
    rw [E.apply_symm_apply]
    apply E.symm.injective
    rw [E.symm_apply_apply, CycleQ2HodgeDerivedTopTrace.derivedTrace_symm,
      CycleQ2HodgeDerivedTopTrace.derivedTrace_symm]
    exact generator_smul φ h c a

end CycleQ2HodgeTopTraceScalars
end

#print axioms CycleQ2HodgeTopTraceScalars.structureTraceLinear
