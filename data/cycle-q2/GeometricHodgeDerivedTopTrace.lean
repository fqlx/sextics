import Proposal.GeometricFourOpenStructureHThree
import Proposal.GeometricHodgeTopCech
import Proposal.GeometricHodgeTwistCoordinates

/-!
# The coefficient trace on the derived top cohomology of the sextic

Expansion on the full overlap and its four faces identifies the signed
Mayer–Vietoris boundary with the Laurent Čech differential. The coefficient
of the all-negative monomial therefore descends to the derived group.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeDerivedTopTrace

open CategoryTheory TopologicalSpace Opposite
  CycleQ2FourOpenHThree CycleQ2HodgeTwistCoordinates CycleQ2HodgeTwistCech
  CycleQ2GeometricSheafLocalIso CycleQ2InjectiveCech

variable {X : TopCat.{0}} {A : Type} [AddCommGroup A] {F : AbSheaf X}
    {D : Vertex → Opens X} {C : Chart F D A} (M : HasLaurentSections C 0)

local instance : HasExt.{1} (AbSheaf X) := HasExt.standard _

private theorem common_le {S : Finset Vertex} {W : Opens X} (h : W = S.inf D) : C.common ≤ W := by
  rw [h]
  exact Finset.le_inf fun i _ => C.le i

/-- Actual sections on this intersection, in their Laurent coordinates. -/
private def sectionEquiv (S : Finset Vertex) (hs : S.Nonempty) (W : Opens X)
    (hw : W = S.inf D) : CycleQ2FourOpenHThree.Sections F W ≃+ sections A 0 S := by
  let f := read C (common_le hw)
  have hI : Function.Injective f := by subst W; exact M.injective S hs
  have hR : f.range = sections A 0 S := by subst W; exact M.range_eq S hs
  let g := f.codRestrict (sections A 0 S) (fun x => hR ▸ (show f x ∈ f.range from ⟨x, rfl⟩))
  refine AddEquiv.ofBijective g ⟨fun a b h => hI (congrArg Subtype.val h), ?_⟩
  intro v
  obtain ⟨x, hx⟩ := Eq.mpr (congrArg (fun H : AddSubgroup (NormalForm A) => v.val ∈ H) hR) v.2
  exact ⟨x, Subtype.ext hx⟩

abbrev OpenTop := QuadOpen (D 0) (D 1) (D 2) (D 3)
abbrev OpenFace := Face (D 0) (D 1) (D 2) (D 3)

def topCoordinates : CycleQ2FourOpenHThree.Sections F (OpenTop (D := D)) ≃+
    CycleQ2HodgeTopCech.TopSection A 0 :=
  sectionEquiv M _ Finset.univ_nonempty _ (quad_eq_inf D)

def faceCoordinates (i : Vertex) : CycleQ2FourOpenHThree.Sections F (OpenFace (D := D) i) ≃+
    sections A 0 (Finset.univ.erase i) :=
  sectionEquiv M _ (by fin_cases i <;> decide) _ (face_eq_inf D i)

private theorem read_restriction (i : Vertex) (p : CycleQ2FourOpenHThree.Sections F (OpenFace (D := D) i)) :
    topCoordinates M (restrictFace F (D 0) (D 1) (D 2) (D 3) i p) =
      restrict (Finset.subset_univ _) (faceCoordinates M i p) := by
  apply Subtype.ext
  exact read_res C (common_le (quad_eq_inf D)) (quad_le_face _ _ _ _ i) p

theorem boundary_coordinates (p : CycleQ2FourOpenHThree.Faces F (D 0) (D 1) (D 2) (D 3)) :
    topCoordinates M (boundary F (D 0) (D 1) (D 2) (D 3) p) =
      CycleQ2HodgeTopCech.boundary (fun i => faceCoordinates M i (p i)) := by
  rw [boundary_apply, map_sub, map_add, map_sub]
  simp only [read_restriction, CycleQ2HodgeTopCech.boundary, Fin.sum_univ_four]
  have h₀ : Even (0 : Vertex).val := by decide
  have h₁ : ¬Even (1 : Vertex).val := by decide
  have h₂ : Even (2 : Vertex).val := by decide
  have h₃ : ¬Even (3 : Vertex).val := by decide
  simp only [if_pos h₀, if_neg h₁, if_pos h₂, if_neg h₃, sub_eq_add_neg] <;> abel

def sectionTrace : CycleQ2FourOpenHThree.Sections F (OpenTop (D := D)) →+ A :=
  CycleQ2HodgeTopCech.trace.comp (topCoordinates M).toAddMonoidHom

theorem sectionTrace_eq_zero_iff (x : CycleQ2FourOpenHThree.Sections F (OpenTop (D := D))) :
    sectionTrace M x = 0 ↔ ∃ p, boundary F (D 0) (D 1) (D 2) (D 3) p = x := by
  change CycleQ2HodgeTopCech.trace (topCoordinates M x) = 0 ↔ _
  rw [CycleQ2HodgeTopCech.trace_eq_zero_iff]
  constructor
  · rintro ⟨p, hp⟩
    let q (i : Vertex) := (faceCoordinates M i).symm (p i)
    refine ⟨q, (topCoordinates M).injective ?_⟩
    rw [boundary_coordinates]
    simpa only [q, AddEquiv.apply_symm_apply] using hp
  · rintro ⟨p, rfl⟩
    exact ⟨_, (boundary_coordinates M p).symm⟩

def representative (a : A) : CycleQ2FourOpenHThree.Sections F (OpenTop (D := D)) :=
  (topCoordinates M).symm (CycleQ2HodgeTopCech.representative a)

@[simp] theorem sectionTrace_representative (a : A) : sectionTrace M (representative M a) = a := by
  change CycleQ2HodgeTopCech.trace ((topCoordinates M) ((topCoordinates M).symm _)) = _
  rw [AddEquiv.apply_symm_apply, CycleQ2HodgeTopCech.trace_representative]

private def quotientTrace : CechH3 F (D 0) (D 1) (D 2) (D 3) →+ A :=
  QuotientAddGroup.lift _ (sectionTrace M) fun _ hp => (sectionTrace_eq_zero_iff M _).2 hp

def cechTrace : CechH3 F (D 0) (D 1) (D 2) (D 3) ≃+ A := by
  refine AddEquiv.ofBijective (quotientTrace M) ⟨?_, ?_⟩
  · apply (QuotientAddGroup.injective_lift_iff _ _ _).2
    ext x
    exact (sectionTrace_eq_zero_iff M x).symm
  · intro a
    exact ⟨QuotientAddGroup.mk' _ (representative M a), sectionTrace_representative M a⟩

open AlgebraicGeometry CycleQ2GenericSexticGradient CycleQ2GeometricHodgeThreefold

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (hu : IsUnit (φ vertexCoefficient))
variable {chart : Chart (CycleQ2HodgeFourOpenStructureHThree.O φ) (coordinateOpen φ) R}
  (N : HasLaurentSections chart 0)

/-- The normalized coefficient trace on all third derived cohomology classes. -/
def derivedTrace : (CycleQ2HodgeFourOpenStructureHThree.O φ).H' 3 ⊤ ≃+ R :=
  (CycleQ2HodgeFourOpenStructureHThree.quotientEquiv φ hu).symm.trans (cechTrace N)

/-- Evaluation of the derived trace on the iterated Mayer–Vietoris class of an actual section. -/
theorem derivedTrace_connecting (p : CycleQ2HodgeFourOpenStructureHThree.TopSection φ) :
    derivedTrace φ hu N (CycleQ2HodgeFourOpenStructureHThree.tripleConnecting φ hu p) =
      CycleQ2HodgeTopCech.trace (topCoordinates N p) := by
  let q := QuotientAddGroup.mk' (boundary _ (coordinateOpen φ 0) (coordinateOpen φ 1)
    (coordinateOpen φ 2) (coordinateOpen φ 3)).range p
  let E := CycleQ2HodgeFourOpenStructureHThree.quotientEquiv φ hu
  change cechTrace N (E.symm (E q)) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

/-- The class with trace a is represented on the quadruple overlap by a·w²/(x₀x₁x₂x₃). -/
theorem derivedTrace_symm (a : R) : (derivedTrace φ hu N).symm a =
    CycleQ2HodgeFourOpenStructureHThree.tripleConnecting φ hu (representative N a) := by
  apply (derivedTrace φ hu N).injective
  rw [AddEquiv.apply_symm_apply, derivedTrace_connecting]
  exact (sectionTrace_representative N a).symm

/-- The same coefficient trace in the global Ext definition of ordinary sheaf cohomology. -/
def ordinaryTrace : (CycleQ2HodgeFourOpenStructureHThree.O φ).H 3 ≃+ R :=
  (CycleQ2GeometricSheafCohomologyRestriction.terminalCohomologyEquiv
    (Opens.grothendieckTopology (show TopCat from threefold φ))
    (CycleQ2HodgeFourOpenStructureHThree.O φ) ⊤ CategoryTheory.Limits.isTerminalTop 3).symm.trans
    (derivedTrace φ hu N)

section Fixed

open CycleQ2LiteralFourOpenStructureHThree

variable {fixedChart : Chart CycleQ2LiteralFourOpenStructureHThree.O
    CycleQ2LiteralFourOpenStructureHThree.D ℂ} (P : HasLaurentSections fixedChart 0)

/-- The same comparison on the separately constructed incidence fiber over 57. -/
def fixedTrace : CycleQ2LiteralFourOpenStructureHThree.O.H' 3 ⊤ ≃+ ℂ :=
  CycleQ2LiteralFourOpenStructureHThree.quotientEquiv.symm.trans (cechTrace P)

theorem fixedTrace_connecting (p : CycleQ2LiteralFourOpenStructureHThree.TopSection) :
    fixedTrace P (tripleConnecting p) = CycleQ2HodgeTopCech.trace (topCoordinates P p) := by
  let q := QuotientAddGroup.mk' faceBoundary.range p
  change cechTrace P (quotientEquiv.symm (quotientEquiv q)) = _
  rw [AddEquiv.symm_apply_apply]
  rfl

theorem fixedTrace_symm (a : ℂ) : (fixedTrace P).symm a = tripleConnecting (representative P a) := by
  apply (fixedTrace P).injective
  rw [AddEquiv.apply_symm_apply, fixedTrace_connecting]
  exact (sectionTrace_representative P a).symm

end Fixed

#print axioms fixedTrace_symm
#print axioms ordinaryTrace
#print axioms derivedTrace
#print axioms derivedTrace_symm
end CycleQ2HodgeDerivedTopTrace
end
