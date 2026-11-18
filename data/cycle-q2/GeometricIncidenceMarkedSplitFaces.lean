import Proposal.GeometricIncidenceMarkedFaceProjection
import Proposal.GeometricLiteralMovingPivotCochain
import Proposal.GeometricProjectorTransitionComparison

/-!
# The split moving transitions on the marked incidence faces

Localizing a split edge at the raw matrix pivots preserves its reduction and
its restrictions. The epsilon coefficient of the resulting triple defect
projects to the moving cup on the corresponding projective open.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1500000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2IncidenceMarkedSplitFaces

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
  CycleQ2CartierProjectiveCover CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionKernel CycleQ2LiteralMovingDivisorChern
  CycleQ2LiteralMovingPivotCorrection CycleQ2LiteralMovingPivotCochain
  CycleQ2IncidenceMarkedPivotFaces CycleQ2IncidenceMarkedFaceProjection
  CycleQ2IncidenceMarkedNativeCharts CycleQ2IncidenceMarkedProjectorCharts
  CycleQ2LiteralAbelJacobiMovingFaces CycleQ2GeometricKernelLocalization
  CycleQ2GeometricSquareZeroSplittings CycleQ2SeedSectionAffineInjective
  CycleQ2LiteralNativeDifferentialSections CycleQ2LiteralNativeChernCocycle CycleQ2LiteralNativeGaugeSections
  CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech

attribute [local instance] CycleQ2LiteralProjectiveIntersectionKernel.nativeReductionAlgebra
  CycleQ2GeometricKernelLocalization.localReductionAlgebra
  CycleQ2LiteralIntersectionEpsilonTransport.ordinaryReductionAlgebra

private abbrev X := projectiveSurface 57 1

def chart (S : Face) (hS : S.Nonempty) : Chart :=
  ⟨vertices S, vertices_nonempty hS, nativeLift _ (normalizedProduct S hS)⟩

theorem chart_closed (S : Face) (hS : S.Nonempty) : (chart S hS).closed = faceOpen S hS :=
  congrArg (CycleQ2LiteralMovingPivotPrincipal.principalOpen (vertices S) (vertices_nonempty hS))
    (nativeLift_reduction _ (normalizedProduct S hS))

theorem face_le {S : Face} (hS : S.Nonempty) {a : VertexIndex} (ha : a ∈ S) :
    faceOpen S hS ≤ pivotCover a :=
  (faceOpen_eq S hS).le.trans (Finset.inf_le ha)

private abbrev chart_le {S : Face} (hS : S.Nonempty) {a : VertexIndex} (ha : a ∈ S) :=
  (chart_closed S hS).le.trans (face_le hS ha)

private abbrev denUnit (S : Face) (hS : S.Nonempty) :=
  nativeLift_isUnit S hS (chart S hS).denominator (nativeLift_reduction _ _)

private abbrev thickMap (S : Face) (hS : S.Nonempty) :=
  nativeThickMap (vertices S) (pivotDen S) (chart S hS).denominator (denUnit S hS)

private abbrev chartSection (S : Face) (hS : S.Nonempty) : (chart S hS).C →+* Γ(X,faceOpen S hS) :=
  (X.presheaf.map (homOfLE (chart_closed S hS).ge).op).hom.comp (chart S hS).closedValue.toRingHom

private theorem chartSection_base (S : Face) (hS : S.Nonempty) (x : ClosedRing (vertices S)) :
    chartSection S hS (algebraMap _ _ x) = nativeSection S hS x := by
  change X.presheaf.map (homOfLE (chart_closed S hS).ge).op
    (CycleQ2LiteralMovingPivotPrincipal.closedPrincipalEquiv (vertices S) (vertices_nonempty hS)
      (nativeReduction _ (chart S hS).denominator) (algebraMap _ _ x)) =
    CycleQ2LiteralMovingPivotPrincipal.closedPrincipalEquiv (vertices S) (vertices_nonempty hS)
      (normalizedProduct S hS) (algebraMap _ _ x)
  rw [CycleQ2LiteralMovingPivotPrincipal.closedPrincipalEquiv_base,
    CycleQ2LiteralMovingPivotPrincipal.closedPrincipalEquiv_base]
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp] <;> rfl

variable (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i)

private abbrev nativeUnit (S : Face) (hS : S.Nonempty) (a b : VertexIndex) (ha : a ∈ S) (hb : b ∈ S) :=
  chartUnit (splitLifts t ht) (chart S hS) a b (chart_le hS ha) (chart_le hS hb)

def splitEdge (S : Face) (hS : S.Nonempty) (a b : VertexIndex) (ha : a ∈ S) (hb : b ∈ S) :
    (faceThick S)ˣ :=
  Units.map (thickMap S hS).toMonoidHom (nativeUnit t ht S hS a b ha hb)

private theorem nativeUnit_section (S : Face) (hS : S.Nonempty) (a b : VertexIndex)
    (ha : a ∈ S) (hb : b ∈ S) :
    Units.map (chartSection S hS).toMonoidHom (reducedUnit (C := (chart S hS).C)
      (nativeUnit t ht S hS a b ha hb)) =
    (movingSystem t ht).value (frameAt a _ (face_le hS ha)) (frameAt b _ (face_le hS hb)) := by
  let F := chart S hS
  let h := (chart_closed S hS).ge
  have hE : F.closed ≤ (edgeChart a b).closed :=
    (le_inf (chart_le hS ha) (chart_le hS hb)).trans (edgeChart_open a b).ge
  change Units.map (X.presheaf.map (homOfLE h).op).hom.toMonoidHom
    (Units.map F.closedValue.toMonoidHom (reducedUnit (C := F.C) (onFace (splitLifts t ht) F a b hE))) = _
  rw [onFace_reduction]
  refine ((movingSystem t ht).natural (frameAt a F.closed (chart_le hS ha))
    (frameAt b F.closed (chart_le hS hb)) h).trans ?_
  congr 2

theorem splitEdge_reduction (S : Face) (hS : S.Nonempty) (a b : VertexIndex) (ha : a ∈ S) (hb : b ∈ S) :
    Units.map (faceReduction S).toMonoidHom (splitEdge t ht S hS a b ha hb) =
    Units.map (nativeToFace S hS).toMonoidHom
      ((movingSystem t ht).value (frameAt a _ (face_le hS ha)) (frameAt b _ (face_le hS hb))) := by
  apply Units.ext
  let z := nativeUnit t ht S hS a b ha hb
  refine (nativeThickMap_reduction _ (pivotDen S) _ (denUnit S hS) (z : (chart S hS).E)).trans ?_
  refine (nativeClosedMap_section S hS _ (denUnit S hS) (chartSection S hS) (chartSection_base S hS) _).trans ?_
  exact congrArg (fun u : Γ(X,faceOpen S hS)ˣ => nativeToFace S hS (u : Γ(X,faceOpen S hS)))
    (nativeUnit_section t ht S hS a b ha hb)

private theorem thickRes_trans (A B C : Chart) (hAB : B.closed ≤ A.closed) (hBC : C.closed ≤ B.closed) (x : A.E) :
    Chart.thickRes B C hBC (Chart.thickRes A B hAB x) = Chart.thickRes A C (hBC.trans hAB) x := by
  apply C.thickValue.injective
  rw [Chart.thickRes_value, Chart.thickRes_value, Chart.thickRes_value]
  simp only [← CommRingCat.comp_apply, ← Functor.map_comp] <;> rfl

theorem splitEdge_restrict {S T : Face} (h : S ⊆ T) (hS : S.Nonempty) (hT : T.Nonempty)
    (a b : VertexIndex) (ha : a ∈ S) (hb : b ∈ S) :
    Units.map (faceThickRestrict h).toMonoidHom (splitEdge t ht S hS a b ha hb) =
      splitEdge t ht T hT a b (h ha) (h hb) := by
  let F := chart S hS
  let G := chart T hT
  let hGF : G.closed ≤ F.closed :=
    (chart_closed T hT).le.trans ((faceOpen_mono h hS hT).trans (chart_closed S hS).ge)
  have hFA : F.closed ≤ (edgeChart a b).closed :=
    (le_inf (chart_le hS ha) (chart_le hS hb)).trans (edgeChart_open a b).ge
  apply Units.ext
  refine (nativeThickMap_restrict h F.denominator G.denominator (denUnit S hS) (denUnit T hT)
    (Chart.thickRes F G hGF) (Chart.thickRes_base F G hGF (vertices_mono h))
    (nativeUnit t ht S hS a b ha hb : F.E)).trans ?_
  exact congrArg (thickMap T hT) (thickRes_trans (edgeChart a b) F G hFA hGF
    ((splitLifts t ht).unit a b : (edgeChart a b).E))

open CycleQ2ProjectorTransitionComparison (reduceUnit kernelLog epsilon_kernelLog)

theorem splitFace_cocycle (S : Face) (hS : S.Nonempty) (a b c : VertexIndex)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    reduceUnit (faceReduction S) (splitEdge t ht S hS a b ha hb) *
      reduceUnit (faceReduction S) (splitEdge t ht S hS b c hb hc) =
    reduceUnit (faceReduction S) (splitEdge t ht S hS a c ha hc) := by
  rw [splitEdge_reduction, splitEdge_reduction, splitEdge_reduction, ← map_mul,
    (movingSystem t ht).compose]

theorem splitFace_projection (S : Face) (hS : S.Nonempty) (a b c : VertexIndex)
    (ha : a ∈ S) (hb : b ∈ S) (hc : c ∈ S) :
    faceProjection S hS (kernelLog (faceCoefficients S) (CycleQ2ProjectorTransitionComparison.face
      (splitEdge t ht S hS a b ha hb) (splitEdge t ht S hS b c hb hc) (splitEdge t ht S hS a c ha hc)
      (splitFace_cocycle t ht S hS a b c ha hb hc))).toAdd =
    faceValue coefficientSheaf pivotCover (movingCup t ht) a b c (faceOpen S hS)
      (face_le hS ha) (face_le hS hb) (face_le hS hc) := by
  let F := chart S hS
  let d := chartDefect (splitLifts t ht) F a b c (chart_le hS ha) (chart_le hS hb) (chart_le hS hc)
  let u := nativeUnit t ht S hS a b ha hb
  let v := nativeUnit t ht S hS b c hb hc
  let w := nativeUnit t ht S hS a c ha hc
  let k := CycleQ2ProjectorTransitionComparison.face _ _ _ (splitFace_cocycle t ht S hS a b c ha hb hc)
  have hd : (nativeCoefficients (vertices S) F.denominator).epsilon d = ((u * v * w⁻¹ : F.Eˣ) : F.E) - 1 :=
    epsilon_unitDefect F.kernelEquiv u v w (chartUnit_reduced_cocycle (splitLifts t ht) F a b c _ _ _)
  have hprod : (k.val : faceThick S) = thickMap S hS (((u * v * w⁻¹ : F.Eˣ) : F.E)) := by
    let f := Units.map (thickMap S hS).toMonoidHom
    exact congrArg Units.val (show f u * f v * (f w)⁻¹ = f (u * v * w⁻¹) by rw [map_mul, map_mul, map_inv])
  have hlog : (kernelLog (faceCoefficients S) k).toAdd = nativeClosedMap _ (pivotDen S) _ (denUnit S hS) d := by
    apply (faceCoefficients S).injective
    rw [epsilon_kernelLog, ← nativeThickMap_coefficients (vertices S) (pivotDen S) F.denominator (denUnit S hS) d,
      hd, map_sub, map_one]
    exact congrArg (fun z : faceThick S => z - 1) hprod
  change faceProjection S hS (kernelLog (faceCoefficients S) k).toAdd = _
  rw [hlog, nativeClosedMap_section S hS _ (denUnit S hS) (chartSection S hS) (chartSection_base S hS),
    faceProjection_native]
  let h := (chart_closed S hS).ge
  have he := splitLifts_faces_chart t ht F a b c (vertex_mem ha) (vertex_mem hb) (vertex_mem hc)
    (chart_le hS ha) (chart_le hS hb) (chart_le hS hc)
  refine (congrArg (fun x : Γ(X,F.closed) => X.presheaf.map (homOfLE h).op x) he).trans ?_
  exact res_comp coefficientSheaf (le_inf (le_inf (chart_le hS ha) (chart_le hS hb)) (chart_le hS hc)) h _

end CycleQ2IncidenceMarkedSplitFaces
end

#print axioms CycleQ2IncidenceMarkedSplitFaces.splitEdge_reduction
#print axioms CycleQ2IncidenceMarkedSplitFaces.splitEdge_restrict
#print axioms CycleQ2IncidenceMarkedSplitFaces.splitFace_projection
