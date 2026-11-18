import Proposal.GeometricIncidenceMarkedProjectorComparison
import Proposal.GeometricIncidenceMarkedFaceProjection

/-!
# Čech edge corrections from finite pivot faces

A natural section on each ordered edge of each nonempty face determines
an ordinary Čech one-cochain. Its boundary can be checked on the finite
triple faces and then restricted to every common subopen.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2FiniteFaceEdgeDescent

open CategoryTheory TopologicalSpace CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech
  CycleQ2GeometricSheafLocalIso
variable {X : TopCat.{0}} {ι : Type} [DecidableEq ι]
  (F : AbSheaf X) (U : ι → Opens X)
  (O : (S : Finset ι) → S.Nonempty → Opens X)
  (hO : ∀ S hS, O S hS = S.inf U)

abbrev EdgeData := ∀ (S : Finset ι) (hS : S.Nonempty), S → S → Sections F (O S hS)

theorem le_vertex (S : Finset ι) (hS : S.Nonempty) (a : S) : O S hS ≤ U a.val := by
  rw [hO]
  exact Finset.inf_le a.property

theorem face_mono {S T : Finset ι} (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty) :
    O T hT ≤ O S hS := by
  rw [hO, hO]
  exact Finset.le_inf fun a ha => Finset.inf_le (h ha)

def Natural (b : EdgeData F O) : Prop :=
  ∀ {S T : Finset ι} (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty) (a c : S),
    res F (face_mono U O hO h hS hT) (b S hS a c) =
      b T hT ⟨a.val,h a.property⟩ ⟨c.val,h c.property⟩

def Boundary (b : EdgeData F O) (z : Two F U) : Prop :=
  ∀ (S : Finset ι) (hS : S.Nonempty) (a c d : S),
    b S hS c d - b S hS a d + b S hS a c =
      faceValue F U z a.val c.val d.val (O S hS)
        (le_vertex U O hO S hS a) (le_vertex U O hO S hS c) (le_vertex U O hO S hS d)

private theorem pair_le (a c : ι) :
    U a ⊓ U c ≤ O {a,c} (Finset.insert_nonempty _ _) := by rw [hO]; simp

def edgeOne (b : EdgeData F O) : One F U := fun i j =>
  res F (pair_le U O hO i j)
    (b {i,j} (Finset.insert_nonempty _ _) ⟨i,by simp⟩ ⟨j,by simp⟩)

theorem edge_on (b : EdgeData F O) (hn : Natural F U O hO b)
    (S : Finset ι) (hS : S.Nonempty) (i j : S)
    (W : Opens X) (hW : W ≤ O S hS) (hi : W ≤ U i.val) (hj : W ≤ U j.val) :
    edgeValue F U (edgeOne F U O hO b) i.val j.val W hi hj = res F hW (b S hS i j) := by
  have h : {i.val,j.val} ⊆ S := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact i.property
    · exact j.property
  have he := congrArg (res F hW) (hn h (Finset.insert_nonempty _ _) hS ⟨i.val,by simp⟩ ⟨j.val,by simp⟩)
  simpa only [edgeValue, edgeOne, res_comp] using he

theorem edge_boundary (b : EdgeData F O) (hn : Natural F U O hO b)
    (z : Two F U) (hz : Boundary F U O hO b z)
    (i j k : ι) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) (hk : W ≤ U k) :
    boundaryValue F U (edgeOne F U O hO b) i j k W hi hj hk = faceValue F U z i j k W hi hj hk := by
  let S : Finset ι := {i,j,k}
  have hS : S.Nonempty := Finset.insert_nonempty _ _
  let a : S := ⟨i,by simp [S]⟩
  let c : S := ⟨j,by simp [S]⟩
  let d : S := ⟨k,by simp [S]⟩
  have hW : W ≤ O S hS := by
    rw [hO]
    apply Finset.le_inf
    intro v hv
    simp only [S, Finset.mem_insert, Finset.mem_singleton] at hv
    rcases hv with rfl | rfl | rfl <;> assumption
  rw [boundaryValue, edge_on F U O hO b hn S hS c d W hW hj hk,
    edge_on F U O hO b hn S hS a d W hW hi hk, edge_on F U O hO b hn S hS a c W hW hi hj]
  simpa only [map_add, map_sub, faceValue, res_comp] using congrArg (res F hW) (hz S hS a c d)

end CycleQ2FiniteFaceEdgeDescent

namespace CycleQ2IncidenceMarkedCorrectionDescent

open CategoryTheory AlgebraicGeometry TopologicalSpace CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech
open CycleQ2IncidenceMarkedPivotFaces (Face)
open CycleQ2IncidenceMarkedFaceProjection (faceOpen faceOpen_eq sectionRestrict)
open CycleQ2IncidenceMarkedProjectorComparison (pivotTwo marked_trace_of_edge_correction)
open CycleQ2IncidenceMarkedCoefficientSections (Surface OS)
open CycleQ2LiteralMovingDivisorChern (VertexIndex pivotCover movingClass)
open CycleQ2LiteralAbelJacobiMovingFaces (movingCup)
open CycleQ2IncidenceEtaleParameter (seedMap)
open CycleQ2IncidenceRelativeProjectorResidue (regularCoefficient)
open CycleQ2LiteralCotangentTrace (algebraicTrace)
open CycleQ2CanonicalCubicDiagram (cubicH2)
open CycleQ2SeedSectionAffineInjective (ChartRegular)
open CycleQ2IncidenceFirstOrderCanonicalH2 (firstOrderWeightedCubic)
open CycleQ2LiteralCotangentShortExact (cotangentAdditiveShortExact)

local instance : HasExt.{1} (Sheaf (Opens.grothendieckTopology Surface) AddCommGrpCat.{0}) := HasExt.standard _

abbrev EdgeData := ∀ (S : Face) (hS : S.Nonempty), S → S → Γ(Surface,faceOpen S hS)

theorem face_le (S : Face) (hS : S.Nonempty) (a : S) : faceOpen S hS ≤ pivotCover a.val :=
  CycleQ2FiniteFaceEdgeDescent.le_vertex pivotCover faceOpen faceOpen_eq S hS a

def Natural (b : EdgeData) : Prop :=
  ∀ {S T : Face} (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty) (a c : S),
    sectionRestrict h hS hT (b S hS a c) = b T hT ⟨a.val,h a.property⟩ ⟨c.val,h c.property⟩

def Boundary (b : EdgeData) (z : Two OS pivotCover) : Prop :=
  ∀ (S : Face) (hS : S.Nonempty) (a c d : S), b S hS c d - b S hS a d + b S hS a c =
    faceValue OS pivotCover z a.val c.val d.val (faceOpen S hS)
      (face_le S hS a) (face_le S hS c) (face_le S hS d)

def correction (b : EdgeData) : One OS pivotCover :=
  CycleQ2FiniteFaceEdgeDescent.edgeOne OS pivotCover faceOpen faceOpen_eq b

theorem correction_boundary (b : EdgeData) (hn : Natural b) (z : Two OS pivotCover)
    (hb : Boundary b z) (i j k : VertexIndex) (W : Surface.Opens) (hi : W ≤ pivotCover i)
    (hj : W ≤ pivotCover j) (hk : W ≤ pivotCover k) :
    boundaryValue OS pivotCover (correction b) i j k W hi hj hk =
      faceValue OS pivotCover z i j k W hi hj hk :=
  CycleQ2FiniteFaceEdgeDescent.edge_boundary OS pivotCover faceOpen faceOpen_eq b
    (fun {_ _} h hS hT a c => hn h hS hT a c) z
    (fun S hS a c d => hb S hS a c d) i j k W hi hj hk

theorem marked_trace_of_face_correction (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (b : EdgeData) (hn : Natural b) (hb : Boundary b (pivotTwo - movingCup t ht)) :
    seedMap regularCoefficient = algebraicTrace (cubicH2 firstOrderWeightedCubic
      ((movingClass t ht).comp cotangentAdditiveShortExact.extClass rfl)) :=
  marked_trace_of_edge_correction t ht (correction b) (correction_boundary b hn _ hb)

end CycleQ2IncidenceMarkedCorrectionDescent
end

#print axioms CycleQ2IncidenceMarkedCorrectionDescent.marked_trace_of_face_correction
