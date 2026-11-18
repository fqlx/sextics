import Proposal.GeometricLiteralAbelJacobiQAffineForms
import Proposal.GeometricLiteralAbelJacobiEvaluationAffine

/-!
# Evaluation of a native affine two-form on every subopen

Realization of an ordinary affine exterior form agrees with restriction
of its global section. The sheaf evaluation of a parameter vector therefore
restricts the ordinary contraction on every inverse-image open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2LiteralAbelJacobiQAffineEvaluation

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2LiteralAbelJacobiQAffineForms CycleQ2LiteralAbelJacobiEvaluationAffine
  CycleQ2GeometricAffineDifferentialSheaf CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricSheafKaehlerMap CycleQ2GeometricAffineOverlap
  CycleQ2GeometricExteriorSheaf CycleQ2ExteriorSectionNaturality

variable (S : Type) [CommRing S] [Algebra ℂ S]

private theorem nativeTop (w : ⋀[S]^2 (KaehlerDifferential ℂ S)) :
    nativeRealize S ⊤ 2 w = globalTwo S w := by
  let f := algebraMap S (AffineSections S ⊤)
  let m := affineDifferentialSheaf S
  let d := affineUniversalDifferential S
  let u := sectionLiftSemilinear (Spec.structureSheaf S) (affineCoefficient S) m d ⊤ f (fun _ => rfl)
  let v : KaehlerDifferential ℂ S →ₛₗ[f] m.val.obj (op ⊤) :=
    { toFun := globalForm S, map_add' := (globalForm S).map_add, map_smul' := (globalForm S).map_smul }
  have huv : u = v := by
    apply LinearMap.ext
    intro η
    exact DFunLike.congr_fun (sectionLift_unique (Spec.structureSheaf S) (affineCoefficient S)
      m d ⊤ f (fun _ => rfl) (globalForm S).toAddMonoidHom
      ((globalForm S).map_smul) (globalKaehlerMap_D m d)) η
  change exteriorSection (Spec.structureSheaf S) m.val 2 ⊤ (exteriorMap f u 2 w) =
    exteriorSection (Spec.structureSheaf S) m.val 2 ⊤ (exteriorMap f v 2 w)
  rw [huv]

theorem nativeRestrict (O : (affineScheme S).Opens) (w : ⋀[S]^2 (KaehlerDifferential ℂ S)) :
    nativeRealize S O 2 w =
      (exteriorSheaf (Spec.structureSheaf S) (affineDifferentialSheaf S).val 2).val.map
        (homOfLE (show O ≤ ⊤ from le_top)).op (globalTwo S w) := by
  rw [← nativeTop]
  have h := exteriorSectionLift_restriction (Spec.structureSheaf S) (affineCoefficient S)
    (affineDifferentialSheaf S) (affineUniversalDifferential S) ⊤ (algebraMap S (AffineSections S ⊤))
    (fun _ => rfl) O le_top (algebraMap S (AffineSections S O)) (fun _ => rfl)
    (AlgHom.id ℂ S) (fun _ => rfl) 2 w
  have hId : exteriorDifferentialMap (AlgHom.id ℂ S) 2 w = w :=
    exteriorMap_identity _ (differentialSemilinearMap (AlgHom.id ℂ S)) (fun _ => rfl)
      (fun η => differentialMap_id η) 2 w
  rw [hId] at h
  exact h.symm

variable {B A : Type} [CommRing B] [CommRing A] [Algebra ℂ B] [Algebra ℂ A]
  [Algebra B A] [IsScalarTower ℂ B A]

theorem evaluate_native (v : Derivation ℂ B A) (O : (affineScheme B).Opens)
    (w : ⋀[B]^2 (KaehlerDifferential ℂ B)) :
    (evaluation v).val.app (op O) (nativeRealize B O 2 w) =
      (affineDifferentialSheaf A).val.map
        (homOfLE (show reduction B A ⁻¹ᵁ O ≤ ⊤ from le_top)).op
        (globalForm A (CycleQ2LiteralAbelJacobiContraction.contractRestrict v w)) := by
  rw [nativeRestrict, evaluation_restrict, evaluation_top] <;> rfl

end CycleQ2LiteralAbelJacobiQAffineEvaluation
end

#print axioms CycleQ2LiteralAbelJacobiQAffineEvaluation.evaluate_native

