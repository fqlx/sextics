import Proposal.GeometricLiteralCurvePositiveTwistFractions
import Proposal.GeometricAffineCohomology
import Proposal.GeometricSurfaceResidueFunctoriality

/-!
# Vanishing of H¹ of positive twists on the original curve

On the genus-four complete intersection at r = 57 the two coordinate
frames identify restrictions in the actual sheaf O_C(k) with the
homogeneous denominators. For k ≥ 2 their difference spans all overlap
sections. Affine-chart vanishing and Mayer–Vietoris give the result in
derived sheaf cohomology.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralCurvePositiveTwist

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricProjectiveCurve CycleQ2GeometricProjectiveHOne
  CycleQ2GeometricConeCech.HZero CycleQ2ClosedSupportCohomology

private abbrev C := projectiveCurve 57 1
private abbrev U := firstProjectivePatch 57 1
private abbrev V := secondProjectivePatch 57 1
private abbrev W := overlapProjectivePatch 57 1
private abbrev hW := overlapProjectivePatch_eq 57 1
private abbrev t (k : ℕ) := projectiveTransitionUnit 57 1 ^ k

/-- The sheaf of modules O_C(k) in its two homogeneous-coordinate frames. -/
def curveTwistModule (k : ℕ) : SheafOfModules.{0} (TwistedModule.ringSheaf C.sheaf) :=
  TwistedModule.moduleSheaf C.sheaf U V W hW (t k)

/-- The underlying additive sheaf of O_C(k). -/
def curveTwist (k : ℕ) : Sheaf (Opens.grothendieckTopology C) AddCommGrpCat.{0} :=
  Twisted.sheaf C.sheaf U V W hW (t k)

theorem curveTwistModule_toSheaf (k : ℕ) :
    (SheafOfModules.toSheaf (TwistedModule.ringSheaf C.sheaf)).obj (curveTwistModule k) =
      curveTwist k := rfl

def firstTwistFrame (k : ℕ) :
    CycleQ2GeometricSheafLocalIso.PatchIso (curveTwist k) (structureAdditiveSheaf C) U where
  app O h := Twisted.firstLocalSectionsEquiv C.sheaf U V W hW (t k) O h
  naturality hPO hO s :=
    (Twisted.firstLocalSectionsEquiv_naturality C.sheaf U V W hW (t k) hPO hO s).symm

def secondTwistFrame (k : ℕ) :
    CycleQ2GeometricSheafLocalIso.PatchIso (curveTwist k) (structureAdditiveSheaf C) V where
  app O h := Twisted.secondLocalSectionsEquiv C.sheaf U V W hW (t k) O h
  naturality hPO hO s :=
    (Twisted.secondLocalSectionsEquiv_naturality C.sheaf U V W hW (t k) hPO hO s).symm

private abbrev fstLE : W ≤ U := hW.le.trans inf_le_left
private abbrev sndLE : W ≤ V := hW.le.trans inf_le_right

theorem positiveTwist_section_difference (k : ℕ) (hk : 2 ≤ k)
    (z : (curveTwist k).obj.obj (op W)) :
    ∃ (a : (curveTwist k).obj.obj (op U)) (b : (curveTwist k).obj.obj (op V)),
      (curveTwist k).obj.map (homOfLE fstLE).op a -
        (curveTwist k).obj.map (homOfLE sndLE).op b = z := by
  let e := Twisted.firstLocalSectionsEquiv C.sheaf U V W hW (t k) W fstLE
  let i := overlapProjectiveSectionsIso 57 1
  obtain ⟨a,b,hab⟩ := positiveTwist_difference_surjective k hk (i.inv (e z))
  let a' := (Twisted.firstLocalSectionsEquiv C.sheaf U V W hW (t k) U le_rfl).symm ((firstProjectiveSectionsIso 57 1).hom a)
  let b' := (Twisted.secondLocalSectionsEquiv C.sheaf U V W hW (t k) V le_rfl).symm ((secondProjectiveSectionsIso 57 1).hom b)
  refine ⟨a',b',e.injective ?_⟩
  rw [map_sub]
  have ha : e ((curveTwist k).obj.map (homOfLE fstLE).op a') =
      i.hom (firstProjectiveRestriction 57 1 a) := by
    rw [show e ((curveTwist k).obj.map (homOfLE fstLE).op a') =
        C.presheaf.map (homOfLE fstLE).op ((Twisted.firstLocalSectionsEquiv C.sheaf U V W hW (t k) U le_rfl) a') from
      Twisted.firstLocalSectionsEquiv_naturality C.sheaf U V W hW (t k) fstLE le_rfl a']
    simp only [a', AddEquiv.apply_symm_apply]
    exact firstProjectiveRestriction_is_sheaf_restriction 57 1 a
  have hb : e ((curveTwist k).obj.map (homOfLE sndLE).op b') =
      (t k : Γ(C,W)) * i.hom (secondProjectiveRestriction 57 1 b) := by
    have h := Twisted.localSections_transition C.sheaf U V W hW (t k) W le_rfl
      ((curveTwist k).obj.map (homOfLE sndLE).op b')
    refine h.trans (congrArg₂ (fun x y => x * y)
      (Twisted.res_self C.sheaf W (t k : Γ(C,W))) ?_)
    refine (Twisted.secondLocalSectionsEquiv_naturality C.sheaf U V W hW (t k)
      sndLE le_rfl b').trans ?_
    change C.presheaf.map (homOfLE sndLE).op ((Twisted.secondLocalSectionsEquiv C.sheaf U V W hW (t k) V le_rfl) b') = _
    simp only [b', AddEquiv.apply_symm_apply]
    exact secondProjectiveRestriction_is_sheaf_restriction 57 1 b
  rw [ha,hb]
  have h := congrArg i.hom hab
  change i.hom.hom (_ - _ ^ k * _) = i.hom (i.inv (e z)) at h
  rw [map_sub, map_mul, map_pow] at h
  exact h.trans (i.commRingCatIsoToRingEquiv.apply_symm_apply (e z))

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology C) AddCommGrpCat.{0}) :=
  HasExt.standard _

/-- Actual derived cohomology vanishes for every k ≥ 2, including O_C(5). -/
theorem positiveTwistHOne_subsingleton (k : ℕ) (hk : 2 ≤ k) :
    Subsingleton ((curveTwist k).H' 1 ⊤) := by
  let F := curveTwist k
  let S := projectiveMayerVietoris 57 1 (by norm_num)
  let : Subsingleton ((F.cohomologyPresheaf 1).obj (op S.X₂)) :=
    affineFrameHOne_subsingleton (firstProjectiveChart 57 1) F (overIsoOfPatchIso (firstTwistFrame k))
  let : Subsingleton ((F.cohomologyPresheaf 1).obj (op S.X₃)) :=
    affineFrameHOne_subsingleton (secondProjectiveChart 57 1) F (overIsoOfPatchIso (secondTwistFrame k))
  apply subsingleton_of_forall_eq 0
  intro y
  have hnext : S.toBiprod F 1 y = 0 := by
    rw [S.toBiprod_apply]
    have hp : (((F.cohomologyPresheaf 1).map S.f₂₄.op y),
        ((F.cohomologyPresheaf 1).map S.f₃₄.op y)) = (0,0) :=
      Prod.ext (Subsingleton.elim _ _) (Subsingleton.elim _ _)
    rw [hp]
    exact map_zero _
  obtain ⟨x, hx⟩ := (ShortComplex.ab_exact_iff _).mp ((S.sequence_exact F 0 1 rfl).exact 2) y hnext
  have hz := (sectionBoundary_zero_iff F S (sectionsEquiv F W x)).mpr
    (positiveTwist_section_difference k hk (sectionsEquiv F W x))
  change S.δ F 0 1 rfl ((sectionsEquiv F W).symm (sectionsEquiv F W x)) = 0 at hz
  rw [AddEquiv.symm_apply_apply] at hz
  exact hx.symm.trans hz

end CycleQ2LiteralCurvePositiveTwist
end

#print axioms CycleQ2LiteralCurvePositiveTwist.positiveTwistHOne_subsingleton
