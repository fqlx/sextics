import Proposal.ScratchCechSimplexDifferential
import Proposal.ScratchCechChartPresheaf
import Proposal.ScratchCechChartClassPull
import Proposal.ScratchCechSchemeSectionAlgebras
import Proposal.ScratchCechVertexCohomology

/-! # Čech de Rham on native scheme opens

All Čech objects are sections of actual exterior powers of the module of
Kähler differentials on the scheme's affine intersection rings. An exact
coordinate frame is used only at a tuple intersection; the differential is
independent of those choices by naturality. A specified algebra map from
one chart into a function field evaluates the total class. -/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open CycleQ2LogarithmicChartDerivative (pull pull_d)
open CycleQ2LogarithmicDifferential (exteriorD exteriorD_squared)
open CycleQ2CechDeRhamTotalThree

namespace CycleQ2.Cech.Native

variable {k : Type} [CommRing k] {X : Scheme.{0}} (f : X ⟶ Spec (CommRingCat.of k))
    {ι : Type} (U : ι → X.Opens)

abbrev R (W : X.Opens) := (Sections.presheaf f).obj (op W)
abbrev P (n : ℕ) := Chart.forms (Sections.presheaf f) n
abbrev ringAt {p : ℕ} (x : Fin (p+1) → ι) := R f (intersection U x)

/-- The sole geometry input needed to define the exterior derivatives is an
exact coordinate frame on each nonempty tuple intersection. -/
structure Frames (dim : ℕ) where
  basis (p : ℕ) (x : Fin (p+1) → ι) :
    Module.Basis (Fin dim) (ringAt f U x) (KaehlerDifferential k (ringAt f U x))
  coords (p : ℕ) (x : Fin (p+1) → ι) : Fin dim → ringAt f U x
  exact_coord (p : ℕ) (x : Fin (p+1) → ι) (i : Fin dim) :
    basis p x i = KaehlerDifferential.D k (ringAt f U x) (coords p x i)

variable {dim : ℕ} (A : Frames f U dim)

def simplex : SimplexDifferential U (P f) where
  d p q x := exteriorD (A.basis p x) q
  square p q x := exteriorD_squared (A.basis p x) (A.coords p x) (A.exact_coord p x) q
  face p q x j a :=
    (pull_d ((Sections.presheaf f).map (faceRestriction U x j).op).hom
      (A.basis p (x ∘ j.succAbove)) (A.coords p (x ∘ j.succAbove))
      (A.exact_coord p (x ∘ j.succAbove)) (A.basis (p+1) x)
      (A.coords (p+1) x) (A.exact_coord (p+1) x) q a).symm

abbrev double := simplexDouble U (P f) (simplex f U A)

variable (i : ι) {I : Type} [Fintype I] [LinearOrder I]
    (b : Module.Basis I (R f (U i)) (KaehlerDifferential k (R f (U i))))
    (x : I → R f (U i)) (hx : ∀ j, b j = KaehlerDifferential.D k (R f (U i)) (x j))

theorem vertex_d (q : ℕ) (z : Cochain U (P f) 0 q) :
    vertex U (P f (q+1)) i ((double f U A).v 0 q z) =
      exteriorD b q (vertex U (P f q) i z) :=
  vertex_vertical U (P f) (simplex f U A) q i (exteriorD b q) (fun a =>
    (pull_d ((Sections.presheaf f).map (singletonLift U i).op).hom
      (A.basis 0 (fun _ => i)) (A.coords 0 (fun _ => i))
      (A.exact_coord 0 (fun _ => i)) b x hx q a).symm) z

/-- The ordinary degree-three cohomology class on a chosen cover member. -/
def vertexClass : HThree (double f U A) →+
    LocalCohomology _ _ _ (exteriorD b 2) (exteriorD b 3) (exteriorD_squared b x hx 2) :=
  vertexCohomologyMap _ _ _ _ _ _ _ (vertex U (P f 2) i).hom
    (vertex U (P f 3) i).hom (vertex U (P f 4) i).hom
    (fun a => (vertex_d f U A i b x hx 2 a).symm)
    (fun a => (vertex_d f U A i b x hx 3 a).symm)

/-- A total boundary admits an actual two-form primitive after restriction
to the chosen function field. -/
theorem rationalPrimitive {K : Type} [Field K] [Algebra k K]
    (π : R f (U i) →ₐ[k] K) {J : Type} [Fintype J] [LinearOrder J]
    (c : Module.Basis J K (KaehlerDifferential k K))
    (y : J → K) (hy : ∀ j, c j = KaehlerDifferential.D k K (y j))
    (z : Cycles (double f U A)) (hz : classOf _ z = 0) :
    ∃ η : CycleQ2LogarithmicPullback.Forms k K 2, exteriorD c 2 η =
      pull π 3 (vertex U (P f 3) i z.1.1) := by
  obtain ⟨a,ha⟩ := vertex_exact _ z hz
  refine ⟨pull π 2 (vertex U (P f 2) i a),?_⟩
  rw [pull_d π b x hx c y hy]
  rw [← vertex_d f U A i b x hx 2, ha]

end CycleQ2.Cech.Native
end

#print axioms CycleQ2.Cech.Native.double
#print axioms CycleQ2.Cech.Native.vertexClass
#print axioms CycleQ2.Cech.Native.rationalPrimitive
