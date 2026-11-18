import Proposal.GeometricAffineCohomologyLocalVanishing
import Proposal.GeometricAffineHigherChartRestriction
import Mathlib.CategoryTheory.Sites.SheafCohomology.MayerVietoris
import Mathlib.Topology.Sheaves.MayerVietoris

/-!
# Positive-degree cohomology of the affine structure sheaf

The elements whose principal opens kill a class form an ideal. Closure
under addition follows from binary Mayer–Vietoris and vanishing one degree
lower on the intersection. Local triviality makes the ideal the unit ideal.
Induction starts with the affine degree-one theorem.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GeometricAffineHThree

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits
  Opposite TopologicalSpace AlgebraicGeometry
open CycleQ2GeometricAffineCohomology CycleQ2GeometricProjectiveHOne
  CycleQ2GeometricSheafCohomologyRestriction

section Empty
variable {X : TopCat.{0}} (F : X.Sheaf AddCommGrpCat.{0})
  [HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})]

/-- Cohomology on the empty open is zero in every degree. -/
private theorem empty_subsingleton (n : ℕ) : Subsingleton (F.H' n ⊥) := by
  let J := Opens.grothendieckTopology X
  let Q := freeAbelianSheaf J ⊥
  have hQ : Subsingleton (Q.obj.obj (op ⊥)) :=
    AddCommGrpCat.subsingleton_of_isZero (TopCat.Sheaf.isTerminalOfEmpty Q).isZero
  have h : 𝟙 Q = 0 := (freeSheafSections J ⊥ Q).injective (hQ.elim _ _)
  apply subsingleton_of_forall_eq 0
  intro x
  calc
    x = (Ext.mk₀ (𝟙 Q)).comp x (zero_add n) := (Ext.mk₀_id_comp x).symm
    _ = 0 := by rw [h, Ext.mk₀_zero, Ext.zero_comp]
end Empty

variable (A : Type) [CommRing A]
local instance : HasExt.{1} (AbSheaf A) := HasExt.standard _

private abbrev H (n : ℕ) (U : Opens (PrimeSpectrum A)) := (additiveStructureSheaf A).H' n U

section Frame
local instance (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- A trivialization on an affine chart transports affine vanishing in the same degree. -/
private theorem frame_subsingleton {X : Scheme.{0}} {U : X.Opens} {B : Type} [CommRing B]
    (e : U.toScheme ≅ Spec (CommRingCat.of B)) (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (frame : F.over U ≅ (structureAdditiveSheaf X).over U) (n : ℕ)
    (hB : Subsingleton ((additiveStructureSheaf B).H n)) : Subsingleton (F.H' n U) := by
  let : Subsingleton ((structureAdditiveSheaf (Spec (CommRingCat.of B))).H n) := hB
  exact Function.Injective.subsingleton
    (chartCohomologyEquiv (Opens.grothendieckTopology X) U
      (Opens.grothendieckTopology (Spec (CommRingCat.of B))) (CycleQ2GeometricAffineChartSections.chartOpensEquiv e)
      ⊤ isTerminalTop F (structureAdditiveSheaf (Spec (CommRingCat.of B)))
      (frame ≪≫ chartStructureOverIso e) n).injective

end Frame

variable (n : ℕ)

/-- Restriction of a global positive-degree class to an ambient open. -/
private abbrev toOpen (U : Opens (PrimeSpectrum A)) :
    H A (n + 1) ⊤ ⟶ H A (n + 1) U :=
  ((additiveStructureSheaf A).cohomologyPresheaf (n + 1)).map (homOfLE le_top).op

private lemma restrict_toOpen {U V : Opens (PrimeSpectrum A)} (i : U ⟶ V) (x : H A (n + 1) ⊤) :
    ((additiveStructureSheaf A).cohomologyPresheaf (n + 1)).map i.op (toOpen A n V x) = toOpen A n U x := by
  rw [← ConcreteCategory.comp_apply, toOpen, ← Functor.map_comp]
  rfl

private lemma downward {U V : Opens (PrimeSpectrum A)} (h : U ≤ V) (x : H A (n + 1) ⊤)
    (hv : toOpen A n V x = 0) : toOpen A n U x = 0 := by
  rw [← restrict_toOpen A n (homOfLE h), hv, map_zero]

private lemma sup_vanish
    (prev : ∀ (B : Type) [CommRing B], Subsingleton ((additiveStructureSheaf B).H n))
    (f g : A) (x : H A (n + 1) ⊤)
    (hf : toOpen A n (PrimeSpectrum.basicOpen f) x = 0)
    (hg : toOpen A n (PrimeSpectrum.basicOpen g) x = 0) :
    toOpen A n (PrimeSpectrum.basicOpen f ⊔ PrimeSpectrum.basicOpen g) x = 0 := by
  let D := @PrimeSpectrum.basicOpen A _
  let S := Opens.mayerVietorisSquare (T := PrimeSpectrum.Top A) (D f) (D g)
  let F := additiveStructureSheaf A
  let z := toOpen A n S.X₄ x
  have hpair : S.toBiprod F (n + 1) z = 0 := by
    rw [S.toBiprod_apply]
    have h : ((F.cohomologyPresheaf (n + 1)).map S.f₂₄.op z,
        (F.cohomologyPresheaf (n + 1)).map S.f₃₄.op z) = (0,0) :=
      Prod.ext ((restrict_toOpen A n _ _).trans hf) ((restrict_toOpen A n _ _).trans hg)
    rw [h]
    exact map_zero _
  obtain ⟨b, hb⟩ := (ShortComplex.ab_exact_iff _).mp ((S.sequence_exact F n (n + 1) rfl).exact 2) z hpair
  have hprev : Subsingleton (F.H' n S.X₁) := by
    change Subsingleton (F.H' n (PrimeSpectrum.basicOpen f ⊓ PrimeSpectrum.basicOpen g))
    rw [← PrimeSpectrum.basicOpen_mul]
    exact frame_subsingleton (IsAffineOpen.Spec_basicOpen
      (R := CommRingCat.of A) (f * g)).isoSpec F (Iso.refl _)
      n (prev _)
  have hb0 : b = 0 := hprev.elim _ _
  exact hb.symm.trans (by rw [hb0, map_zero])

private def vanishingIdeal
    (prev : ∀ (B : Type) [CommRing B], Subsingleton ((additiveStructureSheaf B).H n))
    (x : H A (n + 1) ⊤) : Ideal A where
  carrier := {f | toOpen A n (PrimeSpectrum.basicOpen f) x = 0}
  zero_mem' := by
    have h := empty_subsingleton (additiveStructureSheaf A) (n + 1)
    rw [Set.mem_ofPred_eq, PrimeSpectrum.basicOpen_zero]
    exact h.elim _ _
  add_mem' := by
    intro f g hf hg
    refine downward A n (V := PrimeSpectrum.basicOpen f ⊔ PrimeSpectrum.basicOpen g) ?_ x
      (sup_vanish A n prev f g x hf hg)
    intro p hp
    by_contra h
    change ¬ (f ∉ p.asIdeal ∨ g ∉ p.asIdeal) at h
    push Not at h
    exact hp (p.asIdeal.add_mem h.1 h.2)
  smul_mem' := fun a f hf => downward A n (PrimeSpectrum.basicOpen_mul_le_right a f) x hf

private theorem next_affine_subsingleton
    (prev : ∀ (B : Type) [CommRing B], Subsingleton ((additiveStructureSheaf B).H n))
    (localZero : ∀ x : H A (n + 1) ⊤, ∃ s : Finset A, Ideal.span (s : Set A) = ⊤ ∧
      ∀ a ∈ s, toOpen A n (PrimeSpectrum.basicOpen a) x = 0) :
    Subsingleton ((additiveStructureSheaf A).H (n + 1)) := by
  let F := additiveStructureSheaf A
  have htop : Subsingleton (F.H' (n + 1) ⊤) := by
    apply subsingleton_of_forall_eq 0
    intro x
    obtain ⟨s, hspan, hvan⟩ := localZero x
    let I := vanishingIdeal A n prev x
    have hi : I = ⊤ := by
      apply top_unique
      rw [← hspan]
      exact Ideal.span_le.mpr (fun _ ha => hvan _ ha)
    have h1 : 1 ∈ I := hi ▸ Submodule.mem_top
    have hz : toOpen A n (PrimeSpectrum.basicOpen (1 : A)) x = 0 := h1
    rw [PrimeSpectrum.basicOpen_one] at hz
    simpa [toOpen] using hz
  exact Function.Injective.subsingleton
    (terminalCohomologyEquiv (Opens.grothendieckTopology (PrimeSpectrum.Top A)) F
      ⊤ isTerminalTop (n + 1)).symm.injective

/-- Every positive-degree cohomology group of an affine structure sheaf vanishes. -/
theorem affine_H_positive_subsingleton (k : ℕ) :
    ∀ (B : Type) [CommRing B], Subsingleton ((additiveStructureSheaf B).H (k + 1)) := by
  induction k with
  | zero =>
    intro B _
    exact affine_H_one_subsingleton B
  | succ k ih =>
    intro B _
    exact next_affine_subsingleton B (k + 1) ih
      (CycleQ2AffineCohomologyLocalVanishing.locally_zero B (additiveStructureSheaf B) (k + 1))

/-- Degree-three vanishing on the affine scheme itself. -/
theorem affine_H_three_subsingleton : Subsingleton ((additiveStructureSheaf A).H 3) :=
  affine_H_positive_subsingleton 2 A

local instance (X : Scheme.{0}) :
    HasExt.{1} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0}) := HasExt.standard _

/-- A frame on an affine chart kills ambient third cohomology on that chart. -/
theorem affineFrameHThree_subsingleton {X : Scheme.{0}} {U : X.Opens}
    {B : Type} [CommRing B] (e : U.toScheme ≅ Spec (CommRingCat.of B))
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0})
    (frame : F.over U ≅ (structureAdditiveSheaf X).over U) : Subsingleton (F.H' 3 U) :=
  frame_subsingleton e F frame 3 (affine_H_three_subsingleton B)

/-- Third cohomology of the ambient structure sheaf on any actual affine open. -/
theorem affineOpenHThree_subsingleton {X : Scheme.{0}} {U : X.Opens} (hU : IsAffineOpen U) :
    Subsingleton ((structureAdditiveSheaf X).H' 3 U) :=
  affineFrameHThree_subsingleton hU.isoSpec _ (Iso.refl _)

#print axioms affineOpenHThree_subsingleton
#print axioms affine_H_positive_subsingleton
#print axioms affine_H_three_subsingleton
#print axioms affineFrameHThree_subsingleton

end CycleQ2GeometricAffineHThree
end
