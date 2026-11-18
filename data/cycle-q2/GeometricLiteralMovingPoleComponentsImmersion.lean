import Proposal.GeometricLiteralMovingDivisorOrbitPullbackIdeal

/-!
# Structure rings of the three translated curves

The translated curve is the original closed curve followed by the inverse
surface automorphism. On an affine open inside its Cartier and coordinate
charts, its structure map has precisely the translated seed ideal as kernel.
The resulting quotient equivalence sends a residue class to the pullback of
its representative to the actual curve.

Prepared for fqlx with OpenAI ChatGPT assistance; see solution.md.
-/

set_option maxHeartbeats 100000
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingPoleComponents

open CategoryTheory AlgebraicGeometry TopologicalSpace
  CycleQ2SeedProjectiveImageCocycle CycleQ2CartierSurfaceGrading
  CycleQ2ProjectiveCartierIdeal CycleQ2LiteralProjectiveIntersections
  CycleQ2LiteralProjectiveIntersectionRestrictions CycleQ2LiteralProjectiveVertexRestrictions
  CycleQ2LiteralNativeCartierFrames CycleQ2LiteralNativeGaugeSections CycleQ2LiteralOrbitChern
  CycleQ2LiteralMovingDivisorOrbitFrames CycleQ2LiteralMovingDivisorOrbitPullback
  CycleQ2LiteralOrbitAction

abbrev seedImmersion : CycleQ2GeometricProjectiveCurve.projectiveCurve 57 1 ⟶ Surface := CycleQ2GeometricLiteralSurface.curveToSurface 57 1

def componentImmersion (z : ℂ) (hz : z^3 = 1) :
    CycleQ2GeometricProjectiveCurve.projectiveCurve 57 1 ⟶ Surface :=
  seedImmersion ≫ (closedProjectiveAction z hz).inv

instance (z : ℂ) (hz : z^3 = 1) : IsClosedImmersion (componentImmersion z hz) := by
  change IsClosedImmersion (CycleQ2GeometricLiteralSurface.curveToSurface 57 1 ≫
    (closedProjectiveAction z hz).inv)
  infer_instance

private theorem cover_affine (v : Vertex) : IsAffineOpen (cover v) :=
  Proj.isAffineOpen_basicOpen (surfaceGrade 57 1) (refinedDenominator 57 1 v.1 v.2)
    (refinedDenominator_homogeneous 57 1 v.1 v.2) (by omega)

private theorem curveKernel_affine (v : Vertex) (V : Surface.Opens) (hV : IsAffineOpen V)
    (hv : V ≤ cover v) :
    RingHom.ker (seedImmersion.app V).hom =
      Ideal.span {Surface.presheaf.map (homOfLE hv).op (refinedSectionGenerator 57 1 v.1 v.2)} := by
  have h := seedImmersion.ker.map_ideal
    (U := ⟨V,hV⟩) (V := ⟨cover v,cover_affine v⟩) hv
  rw [Scheme.Hom.ker_apply, Scheme.Hom.ker_apply] at h
  rw [← h]
  change (RingHom.ker (seedImmersion.app (refinedOpen 57 1 v.1 v.2)).hom).map _ = _
  rw [refinedSectionKernel_principal, Ideal.map_span, Set.image_singleton]
  rfl

private theorem nativeGenerator_section (s : Finset Vertex) (hs : s.Nonempty)
    (v : Vertex) (hv : v ∈ s) :
    closedSectionsEquiv s hs (generator s v hv) =
      Surface.presheaf.map (homOfLE (show closedOpen s ≤ cover v from
        Proj.basicOpen_mono (surfaceGrade 57 1) _ _ ⟨_, closedVertex_factor s v hv⟩)).op
        (refinedSectionGenerator 57 1 v.1 v.2) :=
  congrArg (fun k => k (refinedGenerator 57 1 v.1 v.2))
    (Proj.awayMap_awayToSection (surfaceGrade 57 1)
      (closedProduct_homogeneous (s.erase v)) (closedVertex_factor s v hv))

theorem edgeGenerator_eq_appLE (f : Surface ⟶ Surface) (v : Vertex)
    (W : Surface.Opens) (hv : W ≤ f ⁻¹ᵁ cover v) :
    edgeGenerator f v W hv = f.appLE (cover v) W hv (refinedSectionGenerator 57 1 v.1 v.2) := by
  have hsingle : cover v ≤ closedOpen {v} := by
    rw [closedOpen_eq]
    refine le_iInf (fun w => le_iInf (fun hw => ?_))
    obtain rfl := Finset.mem_singleton.mp hw
    exact le_rfl
  let h := hv.trans (f.preimage_mono hsingle)
  change f.appLE (closedOpen {v}) W h (closedSectionsEquiv {v} (Finset.singleton_nonempty v)
    (generator {v} v (Finset.mem_singleton_self v))) = _
  rw [nativeGenerator_section]
  have hle : closedOpen {v} ≤ cover v :=
    Proj.basicOpen_mono (surfaceGrade 57 1) _ _ ⟨_, closedVertex_factor {v} v (by simp)⟩
  change ((Surface.presheaf.map (homOfLE hle).op) ≫ f.appLE (closedOpen {v}) W h)
      (refinedSectionGenerator 57 1 v.1 v.2) = _
  rw [f.map_appLE h (homOfLE hle).op]

private theorem untranslate_generator (a : Surface ≅ Surface) (v : Vertex) (W : Surface.Opens)
    (hv : W ≤ a.hom ⁻¹ᵁ cover v)
    (hv' : a.inv ⁻¹ᵁ W ≤ cover v) :
    a.inv.app W (edgeGenerator a.hom v W hv) =
      Surface.presheaf.map (homOfLE hv').op (refinedSectionGenerator 57 1 v.1 v.2) := by
  rw [edgeGenerator_eq_appLE, a.inv.app_eq_appLE]
  have h := Scheme.Hom.appLE_comp_appLE a.inv a.hom (cover v) W (a.inv ⁻¹ᵁ W) hv le_rfl
  simp only [Iso.inv_hom_id] at h
  exact ConcreteCategory.congr_hom h _

theorem componentKernel (z : ℂ) (hz : z^3 = 1) (i : Fin 3) (W : Surface.Opens)
    (hi : W ≤ Patch i) (v : Vertex) (hv : W ≤ (closedProjectiveAction z hz).hom ⁻¹ᵁ cover v)
    (hW : IsAffineOpen W) :
    RingHom.ker ((componentImmersion z hz).app W).hom = translateIdeal i W hi z := by
  let a := closedProjectiveAction z hz
  let V := a.inv ⁻¹ᵁ W
  have hv' : V ≤ cover v := by
    have he := a.inv.preimage_mono hv
    rwa [← Scheme.Hom.comp_preimage, Iso.inv_hom_id, Scheme.Hom.id_preimage] at he
  have : IsIso (a.inv.app W) := a.inv.isIso_app W (by
    rw [Scheme.Hom.opensRange_of_isIso]
    exact le_top)
  let e := (asIso (a.inv.app W)).commRingCatIsoToRingEquiv
  have hgen : e (edgeGenerator a.hom v W hv) =
      Surface.presheaf.map (homOfLE hv').op (refinedSectionGenerator 57 1 v.1 v.2) :=
    untranslate_generator a v W hv hv'
  rw [← edgeGenerator_span z hz i W hi v hv]
  change RingHom.ker ((seedImmersion.app V).hom.comp e.toRingHom) = _
  rw [← RingHom.comap_ker, curveKernel_affine v V (hW.preimage a.inv) hv', ← hgen]
  ext x
  change (e x ∈ Ideal.span {e (edgeGenerator a.hom v W hv)}) ↔
    x ∈ Ideal.span {edgeGenerator a.hom v W hv}
  simp only [Ideal.mem_span_singleton]
  constructor
  · rintro ⟨b,hb⟩
    refine ⟨e.symm b, e.injective ?_⟩
    rw [map_mul, RingEquiv.apply_symm_apply]
    exact hb
  · rintro ⟨b,hb⟩
    exact ⟨e b, (congrArg e hb).trans (map_mul e _ _)⟩

def componentQuotientEquiv (z : ℂ) (hz : z^3 = 1) (i : Fin 3) (W : Surface.Opens)
    (hi : W ≤ Patch i) (v : Vertex) (hv : W ≤ (closedProjectiveAction z hz).hom ⁻¹ᵁ cover v)
    (hW : IsAffineOpen W) :
    (Γ(Surface,W) ⧸ translateIdeal i W hi z) ≃+*
      Γ(CycleQ2GeometricProjectiveCurve.projectiveCurve 57 1, (componentImmersion z hz) ⁻¹ᵁ W) :=
  (Ideal.quotEquivOfEq (componentKernel z hz i W hi v hv hW).symm).trans
    (((componentImmersion z hz).app W).hom.quotientKerEquivOfSurjective
      ((componentImmersion z hz).app_surjective W hW))

theorem componentQuotientEquiv_mk (z : ℂ) (hz : z^3 = 1) (i : Fin 3) (W : Surface.Opens)
    (hi : W ≤ Patch i) (v : Vertex) (hv : W ≤ (closedProjectiveAction z hz).hom ⁻¹ᵁ cover v)
    (hW : IsAffineOpen W) (x : Γ(Surface,W)) :
    componentQuotientEquiv z hz i W hi v hv hW (Ideal.Quotient.mk _ x) =
      (componentImmersion z hz).app W x := by
  rw [componentQuotientEquiv, RingEquiv.trans_apply, Ideal.quotEquivOfEq_mk,
    RingHom.quotientKerEquivOfSurjective_apply_mk]

end CycleQ2LiteralMovingPoleComponents

end

#print axioms CycleQ2LiteralMovingPoleComponents.componentKernel
#print axioms CycleQ2LiteralMovingPoleComponents.componentQuotientEquiv_mk
