import Proposal.GeometricHodgeEulerCokernelSplit
import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous

/-! Sections of the sheaf cokernel of a module morphism that admits a
retraction over a specified open. The canonical projection splits on
each subopen and its kernel consists precisely of the image sections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2HodgeEulerRestrictedCokernel

open AlgebraicGeometry CategoryTheory Limits Opposite

variable {X : Scheme.{0}} {M N : X.Modules} (a : M ⟶ N) (U : X.Opens)
abbrev restriction := SheafOfModules.overFunctor X.ringCatSheaf U

local instance : (restriction U).IsLeftAdjoint :=
  (SheafOfModules.overPushforwardOverAdj (R := X.ringCatSheaf) U).isLeftAdjoint

variable (r : (restriction U).obj N ⟶ (restriction U).obj M)
  (hr : (restriction U).map a ≫ r = 𝟙 _)

/-- Native lift of quotient sections over the entire coordinate chart. -/
def representative : (restriction U).obj (cokernel a) ⟶ (restriction U).obj N :=
  CycleQ2HodgeEulerCokernelSplit.lift (restriction U) a r hr

theorem representative_project :
    representative a U r hr ≫ (restriction U).map (cokernel.π a) = 𝟙 _ :=
  CycleQ2HodgeEulerCokernelSplit.lift_project _ _ _ _

theorem project_representative :
    (restriction U).map (cokernel.π a) ≫ representative a U r hr =
      𝟙 _ - r ≫ (restriction U).map a :=
  CycleQ2HodgeEulerCokernelSplit.project_lift _ _ _ _

def representativeAt (V : X.Opens) (hi : V ≤ U) :
    Γ(cokernel a,V) →ₗ[Γ(X,V)] Γ(N,V) :=
  ((representative a U r hr).val.app (op (Over.mk (homOfLE hi)))).hom

theorem representativeAt_project (V : X.Opens) (hi : V ≤ U)
    (s : Γ(cokernel a,V)) :
    (cokernel.π a).app V (representativeAt a U r hr V hi s) = s :=
  congrArg (fun m : (restriction U).obj (cokernel a) ⟶ _ =>
    m.val.app (op (Over.mk (homOfLE hi))) s) (representative_project a U r hr)

theorem project_representativeAt (V : X.Opens) (hi : V ≤ U)
    (s : Γ(N,V)) :
    representativeAt a U r hr V hi ((cokernel.π a).app V s) =
      s - a.app V (r.val.app (op (Over.mk (homOfLE hi))) s) :=
  congrArg (fun m : (restriction U).obj N ⟶ _ =>
    m.val.app (op (Over.mk (homOfLE hi))) s) (project_representative a U r hr)

/-- The map on sections as a linear map over the native commutative ring of sections. -/
def sectionLinear {P Q : X.Modules} (b : P ⟶ Q) (V : X.Opens) :
    Γ(P,V) →ₗ[Γ(X,V)] Γ(Q,V) := (b.val.app (op V)).hom

include r hr in
theorem section_exact (V : X.Opens) (hi : V ≤ U) :
    (sectionLinear a V).range = (sectionLinear (cokernel.π a) V).ker := by
  ext s
  constructor
  · rintro ⟨x, rfl⟩
    exact congrArg (fun m : M ⟶ cokernel a => m.app V x) (cokernel.condition a)
  · intro hs
    refine ⟨r.val.app (op (Over.mk (homOfLE hi))) s, ?_⟩
    have he := project_representativeAt a U r hr V hi s
    change (cokernel.π a).app V s = 0 at hs
    rw [hs, map_zero] at he
    exact (sub_eq_zero.mp he.symm).symm

def linearQuotient {S P Q : Type} [CommRing S] [AddCommGroup P] [AddCommGroup Q]
    [Module S P] [Module S Q] (f : P →ₗ[S] Q) (p : Submodule S P) (hp : p = f.ker)
    (hf : Function.Surjective f) : (P ⧸ p) ≃ₗ[S] Q :=
  (Submodule.quotEquivOfEq _ _ hp).trans (f.quotKerEquivOfSurjective hf)

theorem linearQuotient_mk {S P Q : Type} [CommRing S] [AddCommGroup P] [AddCommGroup Q]
    [Module S P] [Module S Q] (f : P →ₗ[S] Q) (p : Submodule S P) (hp : p = f.ker)
    (hf : Function.Surjective f) (x : P) :
    linearQuotient f p hp hf (Submodule.Quotient.mk x) = f x := by
  simp only [linearQuotient, LinearEquiv.trans_apply, Submodule.quotEquivOfEq_mk,
    LinearMap.quotKerEquivOfSurjective_apply_mk]

def quotientEquiv (V : X.Opens) (hi : V ≤ U) :
    (Γ(N,V) ⧸ (sectionLinear a V).range) ≃ₗ[Γ(X,V)] Γ(cokernel a,V) :=
  linearQuotient (sectionLinear (cokernel.π a) V) _ (section_exact a U r hr V hi)
    (fun s => ⟨_, representativeAt_project a U r hr V hi s⟩)

@[simp] theorem quotientEquiv_mk (V : X.Opens) (hi : V ≤ U) (s : Γ(N,V)) :
    quotientEquiv a U r hr V hi (Submodule.Quotient.mk s) = (cokernel.π a).app V s :=
  linearQuotient_mk _ _ _ _ _

end CycleQ2HodgeEulerRestrictedCokernel
end

#print axioms CycleQ2HodgeEulerRestrictedCokernel.representative_project
#print axioms CycleQ2HodgeEulerRestrictedCokernel.quotientEquiv
