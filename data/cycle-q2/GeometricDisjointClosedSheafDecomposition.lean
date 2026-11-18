import Proposal.GeometricClosedSupportedRestriction
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# Additive sheaves on a finite disjoint union of closed subspaces

The unit maps to the direct images of the restrictions induce an isomorphism
onto their finite product when the original sheaf is supported on the union.
At a support point exactly one factor contributes its original stalk.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2DisjointClosedSheafDecomposition

open CategoryTheory CategoryTheory.Limits Topology TopologicalSpace Opposite
  TopCat.Presheaf CycleQ2ClosedEmbeddingSheafExact CycleQ2ClosedSupportedRestriction

variable {ι : Type} [Fintype ι] [Nonempty ι]
  {Y : TopCat.{0}} {X : ι → TopCat.{0}} (f : ∀ i, X i ⟶ Y)
  (hf : ∀ i, IsClosedEmbedding (f i))

omit [Fintype ι] [Nonempty ι] in
private theorem lift_isIso {A : AddCommGrpCat.{0}} {B : ι → AddCommGrpCat.{0}}
    (m : ∀ i, A ⟶ B i) (k : ι) (hk : IsIso (m k))
    (hzero : ∀ i, i ≠ k → IsZero (B i)) : IsIso (Pi.lift m) := by
  let := hk
  exact ⟨⟨Pi.π B k ≫ inv (m k), by simp, by
    apply Pi.hom_ext
    intro i
    by_cases hi : i = k
    · subst i
      simp
    · apply (hzero i hi).eq_of_tgt⟩⟩

def component (F : Y.Sheaf AddCommGrpCat.{0}) (i : ι) : Y.Sheaf AddCommGrpCat.{0} :=
  (push (f i)).obj (inverseSheaf (f i) F)

def componentMap (F : Y.Sheaf AddCommGrpCat.{0}) : F ⟶ ∏ᶜ (component f F) :=
  Pi.lift (fun i => supportUnit (f i) F)

/-- The product projections of this isomorphism are the canonical restrictions to the
    individual closed components. -/
def decomposition (F : Y.Sheaf AddCommGrpCat.{0})
    (hdisj : Pairwise fun i j => Disjoint (Set.range (f i)) (Set.range (f j)))
    (hsupport : ∀ y, (∀ i, y ∉ Set.range (f i)) →
      Subsingleton (stalk (C := AddCommGrpCat) F.obj y)) :
    F ≅ ∏ᶜ (component f F) := by
  classical
  have : IsIso (componentMap f F) := by
    apply (isIso_iff_stalkFunctor_map_iso _).mpr
    intro y
    let S := TopCat.Sheaf.forget AddCommGrpCat Y ⋙ stalkFunctor AddCommGrpCat y
    change IsIso (S.map (Pi.lift (fun i => supportUnit (f i) F)))
    have off (i : ι) (hy : y ∉ Set.range (f i)) : IsZero (S.obj (component f F i)) :=
      AddCommGrpCat.isZero_iff_subsingleton.mpr (push_stalk_off_range (f i) (hf i) _ hy)
    have hproduct : IsIso (Pi.lift (fun i => S.map (supportUnit (f i) F))) := by
      by_cases hy : ∃ i, y ∈ Set.range (f i)
      · obtain ⟨k,x,rfl⟩ := hy
        apply lift_isIso _ k (supportUnit_stalk_isIso (f k) (hf k) F x)
        intro i hi
        exact off i (fun hx => Set.disjoint_left.mp (hdisj hi) hx ⟨x,rfl⟩)
      · let k : ι := Classical.choice ‹Nonempty ι›
        have ha : ∀ i, y ∉ Set.range (f i) := not_exists.mp hy
        have hz : IsZero (S.obj F) := AddCommGrpCat.isZero_iff_subsingleton.mpr (hsupport y ha)
        apply lift_isIso _ k (isIso_of_source_target_iso_zero _ hz.isoZero (off k (ha k)).isoZero)
        exact fun i _ => off i (ha i)
    let p := piComparison S (component f F)
    have hpS : PreservesFiniteLimits S := by dsimp [S]; infer_instance
    have hp : IsIso p := by
      change IsIso (piComparison S (component f F))
      infer_instance
    have hcompose : IsIso (S.map (Pi.lift (fun i => supportUnit (f i) F)) ≫ p) := by
      change IsIso (S.map (Pi.lift (fun i => supportUnit (f i) F)) ≫ piComparison S _)
      rw [map_lift_piComparison]
      exact hproduct
    exact @IsIso.of_isIso_comp_right _ _ _ _ _ _ p hp hcompose
  exact asIso (componentMap f F)

end CycleQ2DisjointClosedSheafDecomposition

end

#print axioms CycleQ2DisjointClosedSheafDecomposition.decomposition
