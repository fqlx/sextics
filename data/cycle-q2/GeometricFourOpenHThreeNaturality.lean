import Proposal.GeometricFourOpenStructureHThree
import Proposal.GeometricThreeOpenH2Naturality

/-!
# Naturality of the four-open top connecting class

An additive-sheaf morphism carries the section on the quadruple overlap
to its original image and commutes with the three successive boundaries.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2FourOpenHThreeNaturality

open CategoryTheory TopologicalSpace Opposite CycleQ2FourOpenHThree
open CycleQ2GeometricCanonicalCechBoundary
open CycleQ2ThreeOpenH2Naturality (cohomologyMap)

variable {X : TopCat.{0}} [HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})]
variable {F G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}}
variable (f : F ⟶ G) (U V W Z : Opens X) (p : Sections F (QuadOpen U V W Z))

theorem connecting_naturality :
    cohomologyMap f 3 (((U ⊔ V) ⊔ W) ⊔ Z) (connecting F U V W Z p) =
      connecting G U V W Z (f.hom.app (op (QuadOpen U V W Z)) p) := by
  let S := Opens.mayerVietorisSquare' (T := X)
    { X₁ := ((U ⊓ Z) ⊔ (V ⊓ Z)) ⊔ (W ⊓ Z)
      X₂ := (U ⊔ V) ⊔ W
      X₃ := Z
      X₄ := ((U ⊔ V) ⊔ W) ⊔ Z
      f₁₂ := homOfLE (sup_le_sup (sup_le_sup inf_le_left inf_le_left) inf_le_left)
      f₁₃ := homOfLE (sup_le (sup_le inf_le_right inf_le_right) inf_le_right)
      f₂₄ := homOfLE le_sup_left
      f₃₄ := homOfLE le_sup_right
      fac := Subsingleton.elim _ _ }
    rfl (by simp only [inf_sup_right])
  let y := CycleQ2ThreeOpenSectionH2.connecting F (U ⊓ Z) (V ⊓ Z) (W ⊓ Z) p
  change cohomologyMap f 3 S.X₄ (S.δ F 2 3 rfl y) =
    S.δ G 2 3 rfl (CycleQ2ThreeOpenSectionH2.connecting G (U ⊓ Z) (V ⊓ Z) (W ⊓ Z) _)
  exact (mayerVietoris_delta_naturality f S 2 3 rfl y).trans (congrArg (S.δ G 2 3 rfl)
    (CycleQ2ThreeOpenH2Naturality.connecting_naturality f (U ⊓ Z) (V ⊓ Z) (W ⊓ Z) p))

/-- Coefficient naturality of the genuine H³ class after transport to the top open. -/
theorem connectingAtTop_naturality (hc : ((U ⊔ V) ⊔ W) ⊔ Z = ⊤) :
    cohomologyMap f 3 ⊤ (connectingAtTop F U V W Z hc p) =
      connectingAtTop G U V W Z hc (f.hom.app (op (QuadOpen U V W Z)) p) := by
  let α := (Sheaf.cohomologyPresheafFunctor (Opens.grothendieckTopology X) 3).map f
  have h := ConcreteCategory.congr_hom (α.naturality (eqToIso hc.symm).op.hom) (connecting F U V W Z p)
  change cohomologyMap f 3 ⊤ (connectingAtTop F U V W Z hc p) =
      (G.cohomologyPresheaf 3).map (eqToIso hc.symm).op.hom
        (cohomologyMap f 3 (((U ⊔ V) ⊔ W) ⊔ Z) (connecting F U V W Z p)) at h
  exact h.trans (congrArg ((G.cohomologyPresheaf 3).map (eqToIso hc.symm).op.hom)
    (connecting_naturality f U V W Z p))

#print axioms connectingAtTop_naturality
end CycleQ2FourOpenHThreeNaturality
end
