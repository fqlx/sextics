import Proposal.GeometricHodgeEulerTangentDescent
import Proposal.GeometricHodgeEulerTripleContraction

/-! Evaluation and contraction of a homogeneous tangent representative
on an actual affine subopen of the projective sextic. This applies in
particular to differences between two local lifts of a normal section.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeEulerTangentRepresentatives

open AlgebraicGeometry CategoryTheory Limits Opposite
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (threefold toBase vertexCoefficient)
open CycleQ2HodgeTwistRatios (U)
open CycleQ2HodgeEulerTangentSheaf CycleQ2HodgeEulerSheaf
open CycleQ2HodgeEulerQuotientSections (rawCoordinate)
open CycleQ2HodgeEulerQuotientFrames (frame frame_project_apply euler ambientEquiv ambientEquiv_apply gradients)
open CycleQ2HodgeEulerTangentToQuotient
open CycleQ2HodgeEulerTangentDescent (quotientTangentIsoOfVertex tangentToQuotientOfVertex tangentToQuotientOfVertex_app)
open CycleQ2GeometricAffineChartSections CycleQ2GeometricDifferentialSheaf
  CycleQ2ChartExteriorBinding CycleQ2LiteralThreefoldResidueContraction
  CycleQ2HodgeEulerContractionSheaf CycleQ2GeometricChartTangentMaps

variable (φ : CoeffRing →+* ℂ) (hv : IsUnit (φ vertexCoefficient)) (W : (threefold φ).Opens)

open CycleQ2SeedSectionSheafLimits (sectionKernelEquiv sectionKernelEquiv_symm_val)
open CycleQ2HodgeThreefoldTwist (chartFrame)

/-- The difference between two local lifts of the same normal section,
as an actual section of the native normal kernel. -/
def liftDifference (s t : Γ(raw φ,W)) (hs : (normalMap φ).app W s = (normalMap φ).app W t) :
    Γ(rawTangent φ,W) :=
  (sectionKernelEquiv (normalMap φ) W).symm ⟨t-s, by
    change (normalMap φ).app W (t-s) = 0
    rw [map_sub, hs, sub_self]⟩

theorem liftDifference_coordinate (i : Fin 4) (hi : W ≤ U φ i)
    (s t : Γ(raw φ,W)) (hs : (normalMap φ).app W s = (normalMap φ).app W t) (j : Fin 5) :
    rawCoordinate φ i W hi j (liftDifference φ W s t hs) =
      chartFrame φ _ i W hi ((Pi.π (pieces φ) j).app W t) -
        chartFrame φ _ i W hi ((Pi.π (pieces φ) j).app W s) := by
  change chartFrame φ _ i W hi ((Pi.π (pieces φ) j).app W ((kernel.ι (normalMap φ)).app W
    ((sectionKernelEquiv (normalMap φ) W).symm _))) = _
  rw [sectionKernelEquiv_symm_val]
  exact (congrArg (chartFrame φ _ i W hi) (((Pi.π (pieces φ) j).app W).hom.map_sub t s)).trans
    ((chartFrame φ _ i W hi).map_sub _ _)

/-- The intrinsic relative tangent class of an actual ambient tangent representative. -/
def intrinsic (v : Γ(rawTangent φ,W)) : Γ(tangent (toBase φ),W) :=
  (quotientTangentIsoOfVertex φ hv).hom.app W ((cokernel.π (radialTangent φ)).app W v)

theorem intrinsic_project (v : Γ(rawTangent φ,W)) :
    (tangentToQuotientOfVertex φ hv).app W (intrinsic φ hv W v) = (cokernel.π (radialTangent φ)).app W v :=
  congrArg (fun m : tangentQuotient φ ⟶ tangentQuotient φ =>
    m.app W ((cokernel.π (radialTangent φ)).app W v)) (quotientTangentIsoOfVertex φ hv).hom_inv_id

theorem intrinsic_coordinate (i : Fin 4) (hi : W ≤ U φ i) (v : Γ(rawTangent φ,W)) (j : Fin 4) :
    values φ i W hi (intrinsic φ hv W v) (i.castSucc.succAbove j) =
      rawCoordinate φ i W hi (i.castSucc.succAbove j) v -
        rawCoordinate φ i W hi i.castSucc v * euler φ i W hi (i.castSucc.succAbove j) := by
  have hq := (tangentToQuotientOfVertex_app φ hv i W hi (intrinsic φ hv W v)).symm.trans
    (intrinsic_project φ hv W v)
  rw [← frame_toQuotient, hq, frame_project_apply]

/-- A normalized five-tuple satisfying the homogeneous gradient equation
defines its canonical actual kernel section on this chart. -/
def rowRepresentative (i : Fin 4) (hi : W ≤ U φ i) (b : Fin 5 → Γ(threefold φ,W))
    (hb : CycleQ2HodgeEuler.pairing (gradients φ i W hi) b = 0) : Γ(rawTangent φ,W) :=
  (ambientEquiv φ i W hi).symm ⟨b,hb⟩

theorem rowRepresentative_coordinate (i : Fin 4) (hi : W ≤ U φ i) (b : Fin 5 → Γ(threefold φ,W))
    (hb : CycleQ2HodgeEuler.pairing (gradients φ i W hi) b = 0) (j : Fin 5) :
    rawCoordinate φ i W hi j (rowRepresentative φ W i hi b hb) = b j := by
  rw [← ambientEquiv_apply, rowRepresentative, LinearEquiv.apply_symm_apply]

theorem intrinsic_row_coordinate (i : Fin 4) (hi : W ≤ U φ i) (b : Fin 5 → Γ(threefold φ,W))
    (hb : CycleQ2HodgeEuler.pairing (gradients φ i W hi) b = 0) (l : Fin 4) :
    values φ i W hi (intrinsic φ hv W (rowRepresentative φ W i hi b hb)) (i.castSucc.succAbove l) =
      b (i.castSucc.succAbove l) - b i.castSucc * euler φ i W hi (i.castSucc.succAbove l) := by
  rw [intrinsic_coordinate, rowRepresentative_coordinate, rowRepresentative_coordinate]

variable {A : Type} [CommRing A] [Algebra ℂ A]
  (e : W.toScheme ≅ Spec (CommRingCat.of A))
  (h : e.inv ≫ W.ι ≫ toBase φ = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))

theorem recovered_coordinate (i : Fin 4) (hi : W ≤ U φ i) (v : Γ(rawTangent φ,W)) (j : Fin 4)
    (z : A) (hz : functions e z = coordinateSection φ i W hi (i.castSucc.succAbove j)) :
    functions e (recover e (toBase φ) h (intrinsic φ hv W v) z) =
      rawCoordinate φ i W hi (i.castSucc.succAbove j) v -
        rawCoordinate φ i W hi i.castSucc v * euler φ i W hi (i.castSucc.succAbove j) := by
  rw [recover_apply]
  change evaluate (toBase φ) _ ((universalDifferential (threefold φ).sheaf (schemeCoefficient (toBase φ))).d
    (X := op W) (chartSection e (chartTop W) z)) = _
  rw [← functions_apply e, hz]
  exact intrinsic_coordinate φ hv W i hi v j

open scoped KaehlerDifferential

/-- Native contraction of a true homogeneous tangent class with an affine three-form. -/
theorem contract_intrinsic (v : Γ(rawTangent φ,W)) (ω : ⋀[A]^3 Ω[A⁄ℂ]) :
    contractSection (cotangent (toBase φ)) W (intrinsic φ hv W v)
        (chartExteriorSheafSection e (toBase φ) h 3 (chartTop W) ω) =
      chartExteriorSheafSection e (toBase φ) h 2 (chartTop W)
        (interior 2 (recover e (toBase φ) h (intrinsic φ hv W v)).liftKaehlerDifferential ω) := by
  have eq := (affineTangentEquiv e (toBase φ) h).apply_symm_apply (intrinsic φ hv W v)
  exact (congrArg (fun s => contractSection (cotangent (toBase φ)) W s
    (chartExteriorSheafSection e (toBase φ) h 3 (chartTop W) ω)) eq.symm).trans
      (contractSection_chart e (toBase φ) h _ ω)

open CycleQ2HodgeEulerTripleContraction (triple affineScalar triple_chart)

/-- Intrinsic evaluation of the three homogeneous normal-lift differences
agrees with the affine scalar obtained from their recovered derivations. -/
theorem triple_intrinsic (v w u : Γ(rawTangent φ,W)) (ω : ⋀[A]^3 Ω[A⁄ℂ]) :
    triple (cotangent (toBase φ)) W (intrinsic φ hv W v) (intrinsic φ hv W w)
        (intrinsic φ hv W u) (chartExteriorSheafSection e (toBase φ) h 3 (chartTop W) ω) =
      functions e (affineScalar (recover e (toBase φ) h (intrinsic φ hv W v))
        (recover e (toBase φ) h (intrinsic φ hv W w))
        (recover e (toBase φ) h (intrinsic φ hv W u)) ω) :=
  triple_chart e (toBase φ) h _ _ _ ω

end CycleQ2HodgeEulerTangentRepresentatives
end
#print axioms CycleQ2HodgeEulerTangentRepresentatives.recovered_coordinate
#print axioms CycleQ2HodgeEulerTangentRepresentatives.contract_intrinsic

#print axioms CycleQ2HodgeEulerTangentRepresentatives.triple_intrinsic
