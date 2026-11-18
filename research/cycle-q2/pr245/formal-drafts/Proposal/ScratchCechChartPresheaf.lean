import Proposal.GeometricLogarithmicChartDerivative
import Proposal.ScratchLogChartComplex
import Mathlib.Algebra.Category.CommAlgCat.Basic

/-! # Relative de Rham presheaf on charts with exact coordinates

The sections really are exterior powers of Kähler differentials of the
coordinate algebras. The restriction maps are the algebra-induced pullbacks
and the differential is exterior differentiation, irrespective of the choices
of frames on the two charts of a restriction map. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
open CategoryTheory Opposite
open CycleQ2LogarithmicChartDerivative (pull pull_d)
open CycleQ2LogarithmicDifferential (exteriorD)
open CycleQ2LogarithmicPullback (Forms differential differential_D)

namespace CycleQ2.Cech.Chart

variable {k S : Type} [CommRing k] [CommRing S] [Algebra k S]

theorem differential_id (ω : KaehlerDifferential k S) :
    differential (AlgHom.id k S) ω = ω := by
  have h : ω ∈ Submodule.span S (Set.range (KaehlerDifferential.D k S)) := by
    rw [KaehlerDifferential.span_range_derivation]
    trivial
  induction h using Submodule.span_induction with
  | mem x hx => obtain ⟨a,rfl⟩ := hx; exact differential_D _ _
  | zero => exact map_zero _
  | add _ _ _ _ hx hy => rw [map_add,hx,hy]
  | smul _ _ _ hx => rw [map_smulₛₗ,hx]; rfl

theorem pull_id (n : ℕ) (ω : Forms k S n) : pull (AlgHom.id k S) n ω = ω :=
  CycleQ2GeometricExteriorSheaf.exteriorMap_identity _ _ (fun _ => rfl) differential_id n ω

variable {C : Type*} [Category C] (R : Cᵒᵖ ⥤ CommAlgCat.{0} k)

/-- Pullbacks of differential forms on the actual coordinate algebras. -/
def forms (n : ℕ) : Cᵒᵖ ⥤ AddCommGrpCat.{0} where
  obj U := AddCommGrpCat.of (Forms k (R.obj U) n)
  map f := AddCommGrpCat.ofHom (pull (R.map f).hom n).toAddMonoidHom
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change pull (R.map (𝟙 U)).hom n x = x
    rw [R.map_id,CommAlgCat.hom_id,pull_id]
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    change pull (R.map (f ≫ g)).hom n x =
      pull (R.map g).hom n (pull (R.map f).hom n x)
    rw [R.map_comp,CommAlgCat.hom_comp]
    exact CycleQ2LogarithmicPullback.restrict_comp _ _ n x

/-- An exact frame is objectwise. Compatibility between coordinate choices
is automatic for the differential forms. -/
structure ExactFrames where
  dim : Cᵒᵖ → ℕ
  basis : ∀ U, Module.Basis (Fin (dim U)) (R.obj U) (KaehlerDifferential k (R.obj U))
  coords : ∀ U, Fin (dim U) → R.obj U
  exact_coord : ∀ U i, basis U i = KaehlerDifferential.D k (R.obj U) (coords U i)

variable (A : ExactFrames R)

/-- The actual exterior derivatives as natural transformations. -/
def d (n : ℕ) : forms R n ⟶ forms R (n+1) where
  app U := AddCommGrpCat.ofHom (exteriorD (A.basis U) n)
  naturality {U V} f := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro x
    exact pull_d (R.map f).hom (A.basis U) (A.coords U) (A.exact_coord U)
      (A.basis V) (A.coords V) (A.exact_coord V) n x

/-- The de Rham complex on the intersection diagram. -/
def complex : CochainComplex (Cᵒᵖ ⥤ AddCommGrpCat.{0}) ℕ :=
  CochainComplex.of (forms R) (d R A) (fun n => by
    apply NatTrans.ext
    funext U
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    exact CycleQ2LogarithmicDifferential.exteriorD_squared (A.basis U)
      (A.coords U) (A.exact_coord U) n)

@[simp] theorem complex_d (n : ℕ) : (complex R A).d n (n+1) = d R A n :=
  CochainComplex.of_d _ _ n

end CycleQ2.Cech.Chart
end

#print axioms CycleQ2.Cech.Chart.complex
