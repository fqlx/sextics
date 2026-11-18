import Proposal.GeometricLiteralMovingPivotCorrection
import Proposal.GeometricLiteralMovingPivotUnitDefect

/-!
# The arbitrary lifted unit defect is the moving Chern cup modulo a boundary

The edge correction is a single cochain on the actual moving pivot
cover. Its restrictions to triples use the structure sheaves of the
original thickening and closed surface.
Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1400000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralMovingPivotCochain

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  CycleQ2GeometricKernelLocalization CycleQ2GeometricSquareZeroSplittings CycleQ2GeometricSheafLocalIso
  CycleQ2LiteralMovingPivotPrincipal CycleQ2LiteralMovingPivotCorrection
  CycleQ2LiteralNativeGaugeSections CycleQ2LiteralNativeChernCocycle CycleQ2LiteralNativeDifferentialSections
  CycleQ2LiteralProjectiveIntersections CycleQ2LiteralProjectiveIntersectionKernel CycleQ2LiteralMovingDivisorChern
  CycleQ2LiteralMovingPivotUnitDefect CycleQ2LiteralAbelJacobiMovingFaces CycleQ2SeedSectionAffineInjective
  CycleQ2InjectiveCech CycleQ2FiniteInjectiveCech CycleQ2FiniteCechDescent

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra

abbrev faceChart (i j k : VertexIndex) : Chart :=
  ⟨vertices i j k, inhabitedVertices i j k, liftDenominator i j k⟩

abbrev edgeChart (i j : VertexIndex) := faceChart i j j

theorem faceChart_open (i j k : VertexIndex) : (faceChart i j k).closed = face i j k := by
  change principalOpen (vertices i j k) (inhabitedVertices i j k) (nativeReduction _ (nativeLift _ (pivotProduct i j k))) = _
  rw [nativeLift_reduction, pivotProduct_open]

theorem edgeChart_open (i j : VertexIndex) : (edgeChart i j).closed = pivotCover i ⊓ pivotCover j := by
  rw [faceChart_open]
  exact inf_eq_left.mpr inf_le_right

private theorem edge_le (i j : VertexIndex) (W : Surface.Opens) (hi : W ≤ pivotCover i) (hj : W ≤ pivotCover j) :
    W ≤ (edgeChart i j).closed := (le_inf hi hj).trans (edgeChart_open i j).ge

private abbrev left (i j : VertexIndex) := (edgeChart_open i j).le.trans inf_le_left
private abbrev right (i j : VertexIndex) := (edgeChart_open i j).le.trans inf_le_right

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

/-- A lift is any choice of thick pair units reducing to the indicated
moving-system transitions. No triple compatibility is imposed upstairs. -/
structure EdgeLifts where
  unit (i j : VertexIndex) : (edgeChart i j).Eˣ
  reduced (i j : VertexIndex) :
    Units.map (edgeChart i j).closedValue.toMonoidHom (reducedUnit (unit i j)) =
      (movingSystem t ht).value (frameAt i _ (left i j)) (frameAt j _ (right i j))

/-- Each pair transition is lifted using the genuine splitting of its
first vertex on that same pair. -/
def splitLifts : EdgeLifts t ht where
  unit i j := Units.map ((edgeChart i j).split i.1 (by simp [edgeChart, faceChart, vertices])).toMonoidHom
    (Units.map (edgeChart i j).closedValue.symm.toMonoidHom ((movingSystem t ht).value
      (frameAt i _ (left i j)) (frameAt j _ (right i j))))
  reduced i j := by
    rw [CycleQ2MovingPivotRingSplittings.reduced_splitUnit _ ((edgeChart i j).split_reduces i.1 _)]
    apply Units.ext
    exact (edgeChart i j).closedValue.apply_symm_apply _

variable {t ht} (L : EdgeLifts t ht)

def correctionOne : One coefficientSheaf pivotCover := fun i j =>
  res coefficientSheaf (edgeChart_open i j).ge ((edgeChart i j).closedValue
    ((edgeChart i j).normalizedEdge i.1 (by simp [edgeChart, faceChart, vertices]) (L.unit i j)))

theorem correctionOne_splitLifts (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    correctionOne (splitLifts t ht) = 0 := by
  funext i j
  unfold correctionOne
  change res coefficientSheaf _ ((edgeChart i j).closedValue
    (unitCorrection (edgeChart i j).kernelEquiv ((edgeChart i j).split i.1 _) _ (Units.map _ _))) = 0
  rw [CycleQ2MovingPivotRingSplittings.unitCorrection_splitUnit, map_zero, map_zero]

section RestrictEdge

variable (F : Chart) (i j : VertexIndex) (h : F.closed ≤ (edgeChart i j).closed)

abbrev onFace := Units.map (Chart.thickRes (edgeChart i j) F h).toMonoidHom (L.unit i j)

theorem onFace_reduction :
    Units.map F.closedValue.toMonoidHom (reducedUnit (C := F.C) (onFace L F i j h)) =
      (movingSystem t ht).value (frameAt i _ (h.trans (left i j))) (frameAt j _ (h.trans (right i j))) := by
  let A := edgeChart i j
  have he : Units.map F.closedValue.toMonoidHom (reducedUnit (C := F.C) (onFace L F i j h)) =
      Units.map (Surface.presheaf.map (homOfLE h).op).hom.toMonoidHom
        (Units.map A.closedValue.toMonoidHom (reducedUnit (C := A.C) (L.unit i j))) := by
    apply Units.ext
    exact (congrArg F.closedValue (Chart.reduce_natural A F h (L.unit i j : A.E)).symm).trans
      (Chart.closedRes_value A F h _)
  refine he.trans ?_
  rw [L.reduced]
  refine ((movingSystem t ht).natural (frameAt i _ (left i j)) (frameAt j _ (right i j)) h).trans ?_
  congr 2

theorem edgeCorrection_on (hst : (edgeChart i j).vertices ⊆ F.vertices)
    (W : Surface.Opens) (hW : W ≤ F.closed) :
    edgeValue coefficientSheaf pivotCover (correctionOne L) i j W
        (hW.trans (h.trans (left i j))) (hW.trans (h.trans (right i j))) =
      res coefficientSheaf hW (F.closedValue (F.normalizedEdge i.1
        (hst (by simp [edgeChart, faceChart, vertices])) (onFace L F i j h))) := by
  let A := edgeChart i j
  let x := A.normalizedEdge i.1 (by simp [A,edgeChart, faceChart, vertices]) (L.unit i j)
  rw [← Chart.normalizedEdge_restrict A F h hst i.1 (by simp [A,edgeChart, faceChart, vertices]) (L.unit i j),
    Chart.closedRes_value]
  change res coefficientSheaf _ (res coefficientSheaf (edgeChart_open i j).ge (A.closedValue x)) =
    res coefficientSheaf hW (res coefficientSheaf h (A.closedValue x))
  rw [res_comp, res_comp]

end RestrictEdge

/-- The pair unit restricted to any native principal chart inside its
two moving pivots. -/
abbrev chartUnit (F : Chart) (a b : VertexIndex) (ha : F.closed ≤ pivotCover a)
    (hb : F.closed ≤ pivotCover b) : F.Eˣ :=
  onFace L F a b (edge_le a b F.closed ha hb)

theorem chartUnit_reduced_cocycle (F : Chart) (a b c : VertexIndex)
    (ha : F.closed ≤ pivotCover a) (hb : F.closed ≤ pivotCover b) (hc : F.closed ≤ pivotCover c) :
    reducedUnit (C := F.C) (chartUnit L F a b ha hb) * reducedUnit (chartUnit L F b c hb hc) =
      reducedUnit (chartUnit L F a c ha hc) := by
  apply Units.ext
  apply F.closedValue.injective
  have he : Units.map F.closedValue.toMonoidHom
      (reducedUnit (C := F.C) (chartUnit L F a b ha hb) * reducedUnit (chartUnit L F b c hb hc)) =
      Units.map F.closedValue.toMonoidHom (reducedUnit (C := F.C) (chartUnit L F a c ha hc)) := by
    rw [map_mul, onFace_reduction, onFace_reduction, onFace_reduction]
    exact (movingSystem t ht).compose _ _ _
  exact congrArg Units.val he

def chartDefect (F : Chart) (a b c : VertexIndex) (ha : F.closed ≤ pivotCover a)
    (hb : F.closed ≤ pivotCover b) (hc : F.closed ≤ pivotCover c) : F.C :=
  unitDefect F.kernelEquiv (chartUnit L F a b ha hb) (chartUnit L F b c hb hc) (chartUnit L F a c ha hc)
    (chartUnit_reduced_cocycle L F a b c ha hb hc)

private theorem subset_chart_edge (F : Chart) (a b : VertexIndex) (ha : a.1 ∈ F.vertices) (hb : b.1 ∈ F.vertices) :
    (edgeChart a b).vertices ⊆ F.vertices := by
  intro x hx
  simp only [edgeChart, faceChart, vertices, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl | rfl
  · exact ha
  · exact hb
  · exact hb

private theorem canonicalCorrection_zero (F : Chart) (a b : VertexIndex)
    (ha' : a.1 ∈ F.vertices) (hb' : b.1 ∈ F.vertices) (ha : F.closed ≤ pivotCover a) (hb : F.closed ≤ pivotCover b) :
    F.normalizedEdge a.1 ha' (chartUnit (splitLifts t ht) F a b ha hb) = 0 := by
  let A := edgeChart a b
  have h := Chart.normalizedEdge_restrict A F (edge_le a b F.closed ha hb)
    (subset_chart_edge F a b ha' hb') a.1 (by simp [A,edgeChart,faceChart,vertices]) ((splitLifts t ht).unit a b)
  refine h.symm.trans ?_
  change Chart.closedRes A F _ (unitCorrection A.kernelEquiv (A.split a.1 _) _ (Units.map _ _)) = 0
  rw [CycleQ2MovingPivotRingSplittings.unitCorrection_splitUnit, map_zero]

/-- The canonical pair lifts on an arbitrary further native pivot chart
compute the moving cup on that very open. -/
theorem splitLifts_faces_chart (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (F : Chart) (a b c : VertexIndex) (ha' : a.1 ∈ F.vertices) (hb' : b.1 ∈ F.vertices)
    (hc' : c.1 ∈ F.vertices) (ha : F.closed ≤ pivotCover a) (hb : F.closed ≤ pivotCover b)
    (hc : F.closed ≤ pivotCover c) :
    F.closedValue (chartDefect (splitLifts t ht) F a b c ha hb hc) =
      faceValue coefficientSheaf pivotCover (movingCup t ht) a b c F.closed ha hb hc := by
  let L := splitLifts t ht
  let u := chartUnit L F a b ha hb
  let v := chartUnit L F b c hb hc
  let w := chartUnit L F a c ha hc
  have self (x : F.C) : sectionValue F.vertices F.nonempty F.denominator F.closed le_rfl x = F.closedValue x :=
    res_self coefficientSheaf F.closed _
  have hv : Units.map (sectionValue F.vertices F.nonempty F.denominator F.closed le_rfl).toMonoidHom
      (reducedUnit (C := F.C) v) = (movingSystem t ht).value (frameAt b F.closed hb) (frameAt c F.closed hc) := by
    apply Units.ext
    exact (self _).trans (congrArg Units.val (onFace_reduction L F b c (edge_le b c F.closed hb hc)))
  have hd := arbitraryLift_face F.vertices F.nonempty F.denominator t ht a b c ha' hb' F.closed le_rfl
    ha hb hc u v w (chartUnit_reduced_cocycle L F a b c ha hb hc) hv
  rw [self, self] at hd
  change F.closedValue (chartDefect L F a b c ha hb hc) =
    F.closedValue (F.normalizedEdge b.1 hb' v - F.normalizedEdge a.1 ha' w + F.normalizedEdge a.1 ha' u) + _ at hd
  rw [canonicalCorrection_zero F b c hb' hc' hb hc, canonicalCorrection_zero F a c ha' hc' ha hc,
    canonicalCorrection_zero F a b ha' hb' ha hb, sub_zero, add_zero, map_zero, zero_add] at hd
  exact hd

section Faces

variable (i j k : VertexIndex)
private abbrev F := faceChart i j k
private abbrev hI := (faceChart_open i j k).le.trans (inf_le_left.trans inf_le_left)
private abbrev hJ := (faceChart_open i j k).le.trans (inf_le_left.trans inf_le_right)
private abbrev hK := (faceChart_open i j k).le.trans inf_le_right
private abbrev ab := edge_le i j _ (hI i j k) (hJ i j k)
private abbrev bc := edge_le j k _ (hJ i j k) (hK i j k)
private abbrev ac := edge_le i k _ (hI i j k) (hK i j k)
private abbrev u := onFace L (F i j k) i j (ab i j k)
private abbrev v := onFace L (F i j k) j k (bc i j k)
private abbrev w := onFace L (F i j k) i k (ac i j k)

theorem reduced_cocycle : reducedUnit (C := (F i j k).C) (u L i j k) *
    reducedUnit (v L i j k) = reducedUnit (w L i j k) := by
  exact chartUnit_reduced_cocycle L (F i j k) i j k (hI i j k) (hJ i j k) (hK i j k)

def defectSection : Γ(Surface,(F i j k).closed) :=
  (F i j k).closedValue (unitDefect (F i j k).kernelEquiv (u L i j k) (v L i j k) (w L i j k)
    (reduced_cocycle L i j k))

private theorem subs (a b : VertexIndex) (ha : a.1 ∈ (F i j k).vertices) (hb : b.1 ∈ (F i j k).vertices) :
    (edgeChart a b).vertices ⊆ (F i j k).vertices :=
  subset_chart_edge (F i j k) a b ha hb

theorem defectSection_corrected (W : Surface.Opens) (hW : W ≤ (F i j k).closed) :
    res coefficientSheaf hW (defectSection L i j k) =
      boundaryValue coefficientSheaf pivotCover (correctionOne L) i j k W
        (hW.trans (hI i j k)) (hW.trans (hJ i j k)) (hW.trans (hK i j k)) +
      faceValue coefficientSheaf pivotCover (movingCup t ht) i j k W
        (hW.trans (hI i j k)) (hW.trans (hJ i j k)) (hW.trans (hK i j k)) := by
  let T := F i j k
  have hi : i.1 ∈ T.vertices := by simp [T,F,faceChart,vertices]
  have hj : j.1 ∈ T.vertices := by simp [T,F,faceChart,vertices]
  have hk : k.1 ∈ T.vertices := by simp [T,F,faceChart,vertices]
  have hv : Units.map (sectionValue T.vertices T.nonempty T.denominator W hW).toMonoidHom
      (reducedUnit (C := T.C) (v L i j k)) =
      (movingSystem t ht).value (frameAt j W (hW.trans (hJ i j k))) (frameAt k W (hW.trans (hK i j k))) := by
    have hv' := congrArg (Units.map (Surface.presheaf.map (homOfLE hW).op).hom.toMonoidHom)
      (onFace_reduction L T j k (bc i j k))
    refine hv'.trans ?_
    refine ((movingSystem t ht).natural (frameAt j _ _) (frameAt k _ _) hW).trans ?_
    congr 2
  have hd := arbitraryLift_face T.vertices T.nonempty T.denominator t ht i j k hi hj W hW
    (hW.trans (hI i j k)) (hW.trans (hJ i j k)) (hW.trans (hK i j k)) (u L i j k) (v L i j k) (w L i j k)
    (reduced_cocycle L i j k) hv
  refine hd.trans (congrArg (· + _) ?_)
  rw [map_add, map_sub]
  unfold boundaryValue
  rw [edgeCorrection_on L T j k (bc i j k) (subs i j k j k hj hk),
      edgeCorrection_on L T i k (ac i j k) (subs i j k i k hi hk),
      edgeCorrection_on L T i j (ab i j k) (subs i j k i j hi hj)]

end Faces

def defectTwo : Two coefficientSheaf pivotCover := fun i j k =>
  res coefficientSheaf (faceChart_open i j k).ge (defectSection L i j k)

/-- An actual edge cochain gives the complete discrepancy from the Chern
cup on all subopens of every moving pivot triple. -/
theorem defectTwo_eq_boundary_add_movingCup (i j k : VertexIndex) (W : Surface.Opens)
    (hi : W ≤ pivotCover i) (hj : W ≤ pivotCover j) (hk : W ≤ pivotCover k) :
    faceValue coefficientSheaf pivotCover (defectTwo L) i j k W hi hj hk =
      boundaryValue coefficientSheaf pivotCover (correctionOne L) i j k W hi hj hk +
        faceValue coefficientSheaf pivotCover (movingCup t ht) i j k W hi hj hk := by
  let h := (le_inf (le_inf hi hj) hk).trans (faceChart_open i j k).ge
  refine (res_comp coefficientSheaf (faceChart_open i j k).ge (le_inf (le_inf hi hj) hk) _).trans ?_
  exact defectSection_corrected L i j k W h

/-- The distinguished split lifts give the moving cup itself, including
its order and sign on the actual ordered pivot triples. -/
theorem splitLifts_faces (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)
    (i j k : VertexIndex) (W : Surface.Opens) (hi : W ≤ pivotCover i)
    (hj : W ≤ pivotCover j) (hk : W ≤ pivotCover k) :
    faceValue coefficientSheaf pivotCover (defectTwo (splitLifts t ht)) i j k W hi hj hk =
      faceValue coefficientSheaf pivotCover (movingCup t ht) i j k W hi hj hk := by
  rw [defectTwo_eq_boundary_add_movingCup, correctionOne_splitLifts]
  unfold boundaryValue edgeValue
  simp

/-- The native primitive in the sign and face convention of the marked
projector comparison, for any cochain identified with the arbitrary
unit defect on the actual pivot cover. -/
theorem correctionOne_boundary_of_face_eq (c : Two coefficientSheaf pivotCover)
    (hc : ∀ i j k W hi hj hk, faceValue coefficientSheaf pivotCover c i j k W hi hj hk =
      faceValue coefficientSheaf pivotCover (defectTwo L) i j k W hi hj hk)
    (i j k : VertexIndex) (W : Surface.Opens)
    (hi : W ≤ pivotCover i) (hj : W ≤ pivotCover j) (hk : W ≤ pivotCover k) :
    boundaryValue coefficientSheaf pivotCover (correctionOne L) i j k W hi hj hk =
      faceValue coefficientSheaf pivotCover (c - movingCup t ht) i j k W hi hj hk := by
  change _ = res coefficientSheaf (le_inf (le_inf hi hj) hk) (c i j k - movingCup t ht i j k)
  rw [map_sub]
  change _ = faceValue coefficientSheaf pivotCover c i j k W hi hj hk -
    faceValue coefficientSheaf pivotCover (movingCup t ht) i j k W hi hj hk
  rw [hc, defectTwo_eq_boundary_add_movingCup, add_sub_cancel_right]

end CycleQ2LiteralMovingPivotCochain
end

#print axioms CycleQ2LiteralMovingPivotCochain.defectTwo_eq_boundary_add_movingCup

#print axioms CycleQ2LiteralMovingPivotCochain.correctionOne_boundary_of_face_eq

#print axioms CycleQ2LiteralMovingPivotCochain.splitLifts_faces

#print axioms CycleQ2LiteralMovingPivotCochain.splitLifts_faces_chart
