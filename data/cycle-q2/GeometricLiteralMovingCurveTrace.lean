import Proposal.GeometricClosedSupportedRestriction
import Proposal.GeometricClosedEmbeddingCohomology
import Proposal.GeometricLiteralMovingQuotientTrace
import Proposal.GeometricOffCurveResidue

/-!
# Residue on cohomology of the moving Cartier curve

Away from the moving curve, allowing poles leaves every canonical form
regular. The cokernel of the regular inclusion therefore has zero stalks
on the complement. It is the direct image of its inverse-image sheaf
on the moving curve. The closed-embedding cohomology comparison carries
the concrete surface boundary trace to classes on the curve itself.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LiteralMovingCurveTrace

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
  AlgebraicGeometry TopCat.Presheaf CycleQ2SeedProjectiveImageCocycle
  CycleQ2SeedSectionSheafCurveBinding CycleQ2SeedSectionAffineInjective
  CycleQ2LiteralMovingResidueExact CycleQ2LiteralMovingQuotientTrace
  CycleQ2ClosedEmbeddingCohomology CycleQ2ClosedSupportedRestriction
open CycleQ2SurfaceCoordinateFrames (CanonicalForms)

variable (t : Fin 3 → ℂ)

private theorem regular_stalk_surjective (y : Surface) (hy : y ∉ Set.range (curveToSurface t).base) :
    Function.Surjective ((stalkFunctor AddCommGrpCat y).map (regularInclusion t).hom) := by
  let j := curveToSurface t
  let U : Surface.Opens := ⟨(Set.range j.base)ᶜ, j.isClosedEmbedding.isClosed_range.isOpen_compl⟩
  have hU : j ⁻¹ᵁ U = ⊥ := by
    apply le_antisymm _ bot_le
    intro x hx
    exact (hx ⟨x,rfl⟩).elim
  intro b
  obtain ⟨V,hV,s,rfl⟩ := exists_germ_eq (residueComplex t).X₂.obj b
  let W := V ⊓ U
  have hW : y ∈ W := ⟨hV,hy⟩
  let r := (residueComplex t).X₂.obj.map (homOfLE (show W ≤ V from inf_le_left)).op s
  obtain ⟨a,ha⟩ := (CycleQ2OffCurveResidue.idealRegularInclusion_bijective j U hU CanonicalForms
    W (show W ≤ U from inf_le_right)).surjective r
  refine ⟨germ (residueComplex t).X₁.obj W y hW a,?_⟩
  have ha' : (regularInclusion t).hom.app (op W) a = r := ha
  exact (stalkFunctor_map_germ_apply (C := AddCommGrpCat) (X := (show TopCat from Surface))
    (F := (residueComplex t).X₁.obj) (G := (residueComplex t).X₂.obj)
    W y hW (regularInclusion t).hom a).trans
    ((congrArg (germ (residueComplex t).X₂.obj W y hW) ha').trans
      (germ_res_apply (residueComplex t).X₂.obj (homOfLE (show W ≤ V from inf_le_left)) y hW s))

theorem quotient_stalk_off (y : Surface) (hy : y ∉ Set.range (curveToSurface t).base) :
    Subsingleton (stalk (C := AddCommGrpCat) (residueQuotient t).obj y) := by
  let g := (residueComplex t).g
  have hg : Epi g := inferInstanceAs (Epi (cokernel.π (regularInclusion t)))
  have hs := (locally_surjective_iff_surjective_on_stalks g.hom).mp
    ((TopCat.Sheaf.isLocallySurjective_iff_epi g).mpr hg) y
  have hcomp : (regularInclusion t).hom ≫ g.hom = 0 :=
    congrArg (fun k => k.hom) (cokernel.condition (regularInclusion t))
  have hz (a : stalk (C := AddCommGrpCat) (residueQuotient t).obj y) : a = 0 := by
    obtain ⟨b,rfl⟩ := hs a
    obtain ⟨c,rfl⟩ := regular_stalk_surjective t y hy b
    have h := congrArg (stalkFunctor AddCommGrpCat y).map hcomp
    rw [Functor.map_comp, Functor.map_zero] at h
    exact ConcreteCategory.congr_hom h c
  exact ⟨fun a b => (hz a).trans (hz b).symm⟩

/-- The actual inverse-image sheaf of adjunction residues on the specialized curve. -/
abbrev curveResidues := inverseSheaf (curveToSurface t).base (residueQuotient t)

def quotientPushIso : residueQuotient t ≅
    (CycleQ2ClosedEmbeddingSheafExact.push (curveToSurface t).base).obj (curveResidues t) :=
  supportedIso (curveToSurface t).base (curveToSurface t).isClosedEmbedding
    (residueQuotient t) (quotient_stalk_off t)

local instance (T : TopCat.{0}) : HasExt.{1}
    (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{0}) := HasExt.standard _

def curveCohomologyEquiv : (curveResidues t).H' 1 ⊤ ≃+ (residueQuotient t).H' 1 ⊤ := by
  let e := (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology Surface) 1).mapIso
    (quotientPushIso t).symm
  exact (pushHEquiv (curveToSurface t).base (curveToSurface t).isClosedEmbedding (curveResidues t) 1).trans
    (e.app (op ⊤)).addCommGroupIsoToAddEquiv

def curveResidueTrace (ht : ∀ i, ChartRegular t i) : (curveResidues t).H' 1 ⊤ →+ ℂ :=
  (residueTrace t ht).comp (curveCohomologyEquiv t).toAddMonoidHom

theorem curveResidueTrace_eq (ht : ∀ i, ChartRegular t i) (x : (residueQuotient t).H' 1 ⊤) :
    curveResidueTrace t ht ((curveCohomologyEquiv t).symm x) =
      CycleQ2LiteralCotangentTrace.algebraicTrace (residueConnecting t ht ⊤ x) :=
  congrArg (residueTrace t ht) ((curveCohomologyEquiv t).apply_symm_apply x)

end CycleQ2LiteralMovingCurveTrace
end

#print axioms CycleQ2LiteralMovingCurveTrace.quotientPushIso
#print axioms CycleQ2LiteralMovingCurveTrace.curveResidueTrace_eq
