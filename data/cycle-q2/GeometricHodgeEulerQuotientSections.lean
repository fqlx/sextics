import Proposal.GeometricHodgeNormalExact
import Proposal.GeometricHodgeEulerRestrictedCokernel

/-! The specific pivot of each weight-one chart gives a retraction of
the native radial map on the entire restricted site. On every subopen
the cokernel has a canonical representative, and its sections are the
ordinary quotient of the actual kernel sections by the radial sections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerQuotientSections

open AlgebraicGeometry CategoryTheory Limits Opposite
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricIncidenceProj
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeThreefoldTwist CycleQ2HodgeTwistRatios CycleQ2HodgeAtlasLine
open CycleQ2HodgeEulerSheaf
open CycleQ2SeedSectionSheafLocal (moduleRes moduleRes_app)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Fin 4)

def rawCoordinate (V : (threefold φ).Opens) (hi : V ≤ U φ i) (j : Fin 5) :
    Γ(rawTangent φ,V) →ₗ[Γ(threefold φ,V)] Γ(threefold φ,V) :=
  (chartFrame φ _ i V hi).toLinearMap ∘ₗ ((Pi.π (pieces φ) j).val.app (op V)).hom ∘ₗ
    ((kernel.ι (normalMap φ)).val.app (op V)).hom

theorem rawCoordinate_restrict {V W : (threefold φ).Opens} (hi : V ≤ U φ i) (hW : W ≤ V)
    (j : Fin 5) (s : Γ(rawTangent φ,V)) :
    rawCoordinate φ i W (hW.trans hi) j (moduleRes _ hW s) =
      restrictRing (X := threefold φ) hW (rawCoordinate φ i V hi j s) := by
  change coordinate _ i W _ ((Pi.π (pieces φ) j).app W
    ((kernel.ι (normalMap φ)).app W (moduleRes _ hW s))) = _
  rw [← moduleRes_app, ← moduleRes_app, coordinate_restrict]
  rfl

def retractionAt (V : (threefold φ).Opens) (hi : V ≤ U φ i) :
    Γ(rawTangent φ,V) →ₗ[Γ(threefold φ,V)] Γ(twist φ 0,V) :=
  (chartFrame φ 0 i V hi).symm.toLinearMap ∘ₗ rawCoordinate φ i V hi i.castSucc

private theorem retractionAt_restrict {V W : (threefold φ).Opens} (hi : V ≤ U φ i) (hW : W ≤ V)
    (s : Γ(rawTangent φ,V)) :
    retractionAt φ i W (hW.trans hi) (moduleRes _ hW s) =
      moduleRes _ hW (retractionAt φ i V hi s) := by
  apply (chartFrame φ 0 i W (hW.trans hi)).injective
  change (chartFrame φ 0 i W _) ((chartFrame φ 0 i W _).symm _) =
    coordinate _ i W _ (moduleRes _ hW _)
  rw [LinearEquiv.apply_symm_apply, coordinate_restrict]
  change _ = restrictRing (X := threefold φ) hW ((chartFrame φ 0 i V hi) ((chartFrame φ 0 i V hi).symm _))
  rw [LinearEquiv.apply_symm_apply]
  exact rawCoordinate_restrict φ i hi hW _ s

theorem retractionAt_radial (V : (threefold φ).Opens) (hi : V ≤ U φ i) (s : Γ(twist φ 0,V)) :
    retractionAt φ i V hi ((radialTangent φ).app V s) = s := by
  apply (chartFrame φ 0 i V hi).injective
  change (chartFrame φ 0 i V hi) ((chartFrame φ 0 i V hi).symm _) = _
  rw [LinearEquiv.apply_symm_apply]
  have hk : (kernel.ι (normalMap φ)).app V ((radialTangent φ).app V s) = (radialMap φ).app V s :=
    congrArg (fun g : twist φ 0 ⟶ raw φ => g.app V s) (kernel.lift_ι _ _ (radial_normal φ))
  change coordinate _ i V hi ((Pi.π (pieces φ) i.castSucc).app V
    ((kernel.ι (normalMap φ)).app V ((radialTangent φ).app V s))) = _
  rw [hk]
  have H := radial_component φ i.castSucc i V s
  rw [normalized_radial_self φ i, one_mul] at H
  exact congrArg (restrictRing (X := threefold φ) (le_inf le_rfl hi)) H

abbrev restrictChart := SheafOfModules.overFunctor (threefold φ).ringCatSheaf (U φ i)

def retraction : (restrictChart φ i).obj (rawTangent φ) ⟶ (restrictChart φ i).obj (twist φ 0) where
  val.app O := ModuleCat.ofHom (retractionAt φ i O.unop.left O.unop.hom.le)
  val.naturality {O P} f := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro s
    exact retractionAt_restrict φ i O.unop.hom.le f.unop.left.le s

theorem radial_retraction : (restrictChart φ i).map (radialTangent φ) ≫ retraction φ i = 𝟙 _ := by
  apply SheafOfModules.hom_ext
  apply PresheafOfModules.hom_ext
  intro O
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  exact retractionAt_radial φ i O.unop.left O.unop.hom.le

/-- Native lift of quotient sections over the entire coordinate chart. -/
abbrev representative :=
  CycleQ2HodgeEulerRestrictedCokernel.representative (radialTangent φ) (U φ i)
    (retraction φ i) (radial_retraction φ i)

theorem representative_project :
    representative φ i ≫ (restrictChart φ i).map (cokernel.π (radialTangent φ)) = 𝟙 _ :=
  CycleQ2HodgeEulerRestrictedCokernel.representative_project _ _ _ _

abbrev representativeAt :=
  CycleQ2HodgeEulerRestrictedCokernel.representativeAt (radialTangent φ) (U φ i)
    (retraction φ i) (radial_retraction φ i)

theorem representativeAt_project (V : (threefold φ).Opens) (hi : V ≤ U φ i)
    (s : Γ(tangentQuotient φ,V)) :
    (cokernel.π (radialTangent φ)).app V (representativeAt φ i V hi s) = s :=
  CycleQ2HodgeEulerRestrictedCokernel.representativeAt_project _ _ _ _ V hi s

/-- Every subopen computes the native projective quotient directly on its sections. -/
abbrev quotientEquiv :=
  CycleQ2HodgeEulerRestrictedCokernel.quotientEquiv (radialTangent φ) (U φ i)
    (retraction φ i) (radial_retraction φ i)

@[simp] theorem quotientEquiv_mk (V : (threefold φ).Opens) (hi : V ≤ U φ i) (s : Γ(rawTangent φ,V)) :
    quotientEquiv φ i V hi (Submodule.Quotient.mk s) = (cokernel.π (radialTangent φ)).app V s :=
  CycleQ2HodgeEulerRestrictedCokernel.quotientEquiv_mk _ _ _ _ V hi s

end CycleQ2HodgeEulerQuotientSections
end

#print axioms CycleQ2HodgeEulerQuotientSections.representative_project
#print axioms CycleQ2HodgeEulerQuotientSections.quotientEquiv
