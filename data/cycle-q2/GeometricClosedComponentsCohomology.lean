import Proposal.GeometricClosedEmbeddingCohomology

/-!
# Cohomology of a finite product of closed direct images

An isomorphism to this product identifies cohomology with the product
of the individual closed-subspace cohomology groups in every degree.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2ClosedComponentsCohomology

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Topology TopologicalSpace
  CycleQ2ClosedEmbeddingSheafExact CycleQ2ClosedEmbeddingCohomology CycleQ2InjectiveCech
attribute [local instance] HasFiniteBiproducts.of_hasFiniteProducts

variable {ι : Type} [Fintype ι] {Y : TopCat.{0}} {X : ι → TopCat.{0}}
  (f : ∀ i, X i ⟶ Y) (hf : ∀ i, IsClosedEmbedding (f i))
  (G : ∀ i, (X i).Sheaf AddCommGrpCat.{0}) {F : Y.Sheaf AddCommGrpCat.{0}}
local instance (T : TopCat.{0}) : HasExt.{1} (AbSheaf T) := HasExt.standard _
local instance (T : TopCat.{0}) : HasExt.{1} (T.Sheaf AddCommGrpCat.{0}) := HasExt.standard _

/-- An additive product decomposition of all cohomology groups along the closed images. -/
def componentHEquiv (e : F ≅ ∏ᶜ (fun i => (push (f i)).obj (G i))) (n : ℕ) :
    Sheaf.H'.{1} F n ⊤ ≃+ (∀ i, Sheaf.H'.{1} (G i) n ⊤) := by
  let Z : ι → Y.Sheaf AddCommGrpCat.{0} := fun i => (push (f i)).obj (G i)
  let A := freeOpen (⊤ : Opens Y)
  let u := e ≪≫ (biproduct.isoProduct Z).symm
  let a := ((extFunctorObj A n).mapIso u).addCommGroupIsoToAddEquiv
  exact (a.trans (Ext.addEquivBiproduct A (biproduct.isBilimit Z) n)).trans
    (AddEquiv.piCongrRight (fun i => (pushHEquiv (f i) (hf i) (G i) n).symm))

end CycleQ2ClosedComponentsCohomology
end

#print axioms CycleQ2ClosedComponentsCohomology.componentHEquiv
