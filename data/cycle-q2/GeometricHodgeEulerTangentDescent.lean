import Proposal.GeometricHodgeEulerTangentAgreement
import Proposal.GeometricHodgeEulerBasicDerivativeFrame
import Proposal.GeometricHodgeEulerTangentCover

/-! The radial quotient of the actual projective normal kernel is the
intrinsic tangent sheaf of the moving weighted sextic on the good
parameter open. The isomorphism differentiates the genuine homogeneous
coordinate functions and is checked on an affine basis of the threefold.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerTangentDescent

open CategoryTheory Opposite AlgebraicGeometry
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold toBase goodParameter vertexCoefficient coordinateOpens_cover)
open CycleQ2GeometricIntrinsicNormal
open CycleQ2HodgeEulerSheaf CycleQ2HodgeTwistRatios (U)
open CycleQ2HodgeEulerTangentSheaf CycleQ2HodgeEulerTangentToQuotient
open CycleQ2HodgeEulerTangentAgreement
open CycleQ2HodgeEulerBasicDerivativeFrame (basicDerivativeFrame basicDerivativeFrame_apply principalOpen_le)

variable (φ : CoeffRing →+* ℂ)
private abbrev T := tangent (toBase φ)
private abbrev Q := CycleQ2HodgeEulerSheaf.tangentQuotient φ

def patch (i : Fin 4) : (T φ).over (U φ i) ⟶ (Q φ).over (U φ i) where
  val.app O := ModuleCat.ofHom (toQuotient φ i O.unop.left O.unop.hom.le)
  val.naturality {O P} h := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    exact toQuotient_restrict φ i O.unop.left O.unop.hom.le h.unop.left.le

def localSection (i : Fin 4) : LocalLinearHom (threefold φ).sheaf (T φ) (Q φ) (U φ i) :=
  (localLinearHomEquiv (threefold φ).sheaf (T φ) (Q φ) (U φ i)).symm (patch φ i)

theorem local_compatible (i j : Fin 4) :
    restrictLocalLinearHom (threefold φ).sheaf (T φ) (Q φ)
      (homOfLE (show U φ i ⊓ U φ j ≤ U φ i from inf_le_left)).op (localSection φ i) =
    restrictLocalLinearHom (threefold φ).sheaf (T φ) (Q φ)
      (homOfLE (show U φ i ⊓ U φ j ≤ U φ j from inf_le_right)).op (localSection φ j) := by
  apply localLinearHom_ext
  intro V s
  exact toQuotient_agree φ i j V.left (V.hom.le.trans inf_le_left) (V.hom.le.trans inf_le_right) s

variable (hv : IsUnit (φ vertexCoefficient))

/-- The intrinsic vector field defines a unique section of the homogeneous Euler quotient. -/
def tangentToQuotientOfVertex : T φ ⟶ Q φ :=
  CycleQ2HodgeEulerTangentCover.glue _ _ (U φ) (coordinateOpens_cover φ hv)
    (localSection φ) (local_compatible φ)

theorem tangentToQuotientOfVertex_app (i : Fin 4) (W : (threefold φ).Opens) (hi : W ≤ U φ i) (s : Γ(T φ,W)) :
    (tangentToQuotientOfVertex φ hv).app W s = toQuotient φ i W hi s :=
  CycleQ2HodgeEulerTangentCover.glue_apply _ _ _ _ _ _ i W hi s

instance isIso_tangentToQuotientOfVertex : IsIso (tangentToQuotientOfVertex φ hv) := by
  apply CycleQ2HodgeEulerTangentCover.iso_of_basis φ _ hv
  rintro ⟨i,z⟩
  let W := CycleQ2HodgeEulerBasicDerivativeFrame.principalOpen φ i z
  let b := basicDerivativeFrame φ i z
  let q := CycleQ2HodgeEulerQuotientFrames.frame φ i W (principalOpen_le φ i z)
  have he (s : Γ(T φ,W)) : q ((tangentToQuotientOfVertex φ hv).app W s) = b s := by
    apply Subtype.ext
    funext l
    rw [tangentToQuotientOfVertex_app φ hv i W (principalOpen_le φ i z)]
    exact (frame_toQuotient φ i W (principalOpen_le φ i z) s l).trans
      (basicDerivativeFrame_apply φ i z s l).symm
  constructor
  · intro s t hst
    apply b.injective
    rw [← he, ← he, hst]
  · intro t
    refine ⟨b.symm (q t), q.injective ?_⟩
    rw [he, Equiv.apply_symm_apply]

/-- The actual cokernel of the radial morphism into the actual normal kernel
is the relative tangent sheaf of the original complex fiber. -/
def quotientTangentIsoOfVertex : CycleQ2HodgeEulerSheaf.tangentQuotient φ ≅ tangent (toBase φ) := (asIso (tangentToQuotientOfVertex φ hv)).symm

variable (hg : IsUnit (φ goodParameter))

include hg in
private theorem vertex_unit : IsUnit (φ vertexCoefficient) := by
  rw [goodParameter, map_mul, IsUnit.mul_iff] at hg
  exact hg.2

abbrev tangentToQuotient : T φ ⟶ Q φ := tangentToQuotientOfVertex φ (vertex_unit φ hg)

theorem tangentToQuotient_app (i : Fin 4) (W : (threefold φ).Opens) (hi : W ≤ U φ i) (s : Γ(T φ,W)) :
    (tangentToQuotient φ hg).app W s = toQuotient φ i W hi s :=
  tangentToQuotientOfVertex_app φ (vertex_unit φ hg) i W hi s

def quotientTangentIso : CycleQ2HodgeEulerSheaf.tangentQuotient φ ≅ tangent (toBase φ) :=
  quotientTangentIsoOfVertex φ (vertex_unit φ hg)

end CycleQ2HodgeEulerTangentDescent
end
#print axioms CycleQ2HodgeEulerTangentDescent.quotientTangentIsoOfVertex
#print axioms CycleQ2HodgeEulerTangentDescent.quotientTangentIso
