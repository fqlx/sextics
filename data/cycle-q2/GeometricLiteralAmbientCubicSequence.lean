import Proposal.GeometricHodgeThreefoldLiteral
import Proposal.GeometricHodgeThreefoldTwist
import Proposal.GeometricHodgeNormalizedRegular
import Proposal.GeometricHodgeAtlasRestriction
import Proposal.GeometricLiteralAmbientCubicQuotient
import Proposal.GeometricGradedCechDescent

/-!
# The cubic Cartier sequence on the fixed threefold

Multiplication by the incidence cubic has coefficients H/xᵢ³ on the four
weight-one charts. Restricting the chart-trivialized line to the original
projective surface gives the quotient. The checked local equations determine
exactness on affine neighborhoods of every point.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxRecDepth 12000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralAmbientCubicSequence

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open CycleQ2GeometricHodgeThreefold CycleQ2GeometricHodgeThreefoldIncidence
  CycleQ2GeometricIncidenceProj CycleQ2LiteralAmbientCylinder
  CycleQ2LiteralThreefoldOrbitAction CycleQ2HodgeThreefoldTwist CycleQ2HodgeAtlasLine

abbrev X := threefold literalEval
abbrev structureOn (Z : Scheme.{0}) : Z.Modules := SheafOfModules.unit Z.ringCatSheaf
abbrev O3 := twist literalEval 3
abbrev cubic := quotient literalEval (pointEquationH point)
theorem cubic_homogeneous : cubic ∈ grade literalEval 3 :=
  quotient_mem_grade _ _ (pointEquationH_homogeneous _)

abbrev embedding := surfaceToNative ≫ (nativeIso point).inv
abbrev restrictedO3 := line (pulled embedding (cocycle literalEval 3))
abbrev directImage := (Scheme.Modules.pushforward embedding).obj restrictedO3

private theorem embedding_eq : embedding = CycleQ2LiteralAmbientSurface.surfaceToFiber ≫ literalIso.inv := by
  rw [← surfaceToNative_toIncidence, literalIso, Iso.trans_inv]
  simp

instance embedding_closed : IsClosedImmersion embedding := by
  rw [embedding_eq]
  letI := CycleQ2LiteralAmbientSurface.surfaceToFiber_isClosedImmersion
  infer_instance

def cubicSection : O3.sections :=
  PresheafOfModules.sectionsMk (fun V => homogeneousSection literalEval cubic cubic_homogeneous V.unop)
    (fun {_ _} f => homogeneousSection_restrict literalEval cubic cubic_homogeneous f.unop.le)

def multiplyCubic : structureOn X ⟶ O3 :=
  (SheafOfModules.unitHomEquiv O3).symm cubicSection

abbrev restrictCubic : O3 ⟶ directImage := restrictLine embedding (cocycle literalEval 3)

abbrev equationOn (i : Fin 4) (V : X.Opens) (hi : V ≤ coordinateOpen literalEval i) :=
  CycleQ2HodgeTwistRatios.normalized literalEval i cubic cubic_homogeneous V hi

theorem multiplyCubic_frame (i : Fin 4) (V : X.Opens) (hi : V ≤ coordinateOpen literalEval i)
    (r : Γ(X,V)) :
    chartFrame literalEval 3 i V hi (multiplyCubic.app V r) = r * equationOn i V hi := by
  change chartFrame literalEval 3 i V hi (r • homogeneousSection literalEval cubic cubic_homogeneous V) = _
  rw [map_smul]
  exact congrArg (fun a : Γ(X,V) => r * a)
    (homogeneousSection_coordinate literalEval cubic cubic_homogeneous i V hi)

private abbrev targetFrame (i : Fin 4) (V : X.Opens) (hi : V ≤ coordinateOpen literalEval i) :=
  frame (pulled embedding (cocycle literalEval 3)) i (embedding ⁻¹ᵁ V) (embedding.preimage_mono hi)

private abbrev restrictCubic_frame :=
  restrictLine_frame (U := coordinateOpen literalEval) embedding (cocycle literalEval 3)

private theorem localEquations (i : Fin 4) (V : X.affineOpens) (hV : V.val ≤ coordinateOpen literalEval i) :
    Function.Injective (multiplyCubic.app V.val) ∧
    Function.Exact (multiplyCubic.app V.val) (restrictCubic.app V.val) ∧
    Function.Surjective (restrictCubic.app V.val) := by
  let e := chartFrame literalEval 3 i V.val hV
  let d := targetFrame i V.val hV
  have ker : RingHom.ker (embedding.app V.val).hom = Ideal.span {equationOn i V.val hV} :=
    CycleQ2LiteralAmbientCubicQuotient.model_kernel_on_affine i V hV
  have regular := CycleQ2HodgeNormalizedRegular.seed_normalized_regular i V.val hV
  refine ⟨?_, ?_, ?_⟩
  · intro a b hab
    have eq := congrArg e hab
    change chartFrame _ _ _ _ _ _ = chartFrame _ _ _ _ _ _ at eq
    rw [multiplyCubic_frame, multiplyCubic_frame] at eq
    exact (mul_cancel_right_mem_nonZeroDivisors regular).mp eq
  · intro s
    constructor
    · intro hs
      have hv : e s ∈ RingHom.ker (embedding.app V.val).hom := by
        change embedding.app V.val (e s) = 0
        rw [← restrictCubic_frame, hs, map_zero]
      rw [ker] at hv
      obtain ⟨a,ha⟩ := Ideal.mem_span_singleton'.mp hv
      refine ⟨a, e.injective ?_⟩
      exact (multiplyCubic_frame i V.val hV a).trans ha
    · rintro ⟨a,rfl⟩
      apply d.injective
      rw [map_zero]
      change targetFrame _ _ _ _ = _
      rw [restrictCubic_frame, multiplyCubic_frame]
      apply RingHom.mem_ker.mp
      rw [ker]
      exact Ideal.mem_span_singleton'.mpr ⟨a,rfl⟩
  · intro s
    obtain ⟨a,ha⟩ := embedding.app_surjective V.val V.property (d s)
    refine ⟨e.symm a, d.injective ?_⟩
    change targetFrame _ _ _ _ = _
    rw [restrictCubic_frame, show chartFrame literalEval 3 i V.val hV = e from rfl,
      LinearEquiv.apply_symm_apply]
    exact ha

private theorem neighborhood (V : X.Opens) (x : X) (hx : x ∈ V) :
    ∃ (i : Fin 4) (W : X.affineOpens), W.val ≤ V ∧ x ∈ W.val ∧ W.val ≤ coordinateOpen literalEval i := by
  obtain ⟨i,hi⟩ := exists_weightOne_not_mem literalEval literal_vertex_unit x
  have hx' : x ∈ V ⊓ coordinateOpen literalEval i := ⟨hx,hi⟩
  obtain ⟨W,hW,hxW,hWV⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens hx'
  exact ⟨i,⟨W,hW⟩,hWV.trans inf_le_left,hxW,hWV.trans inf_le_right⟩

private theorem comp_zero_of_local_exact {A : Scheme.{0}} {L M N : A.Modules}
    (u : L ⟶ M) (v : M ⟶ N)
    (localExact : ∀ (V : A.Opens) (x : A), x ∈ V →
      ∃ W : A.Opens, W ≤ V ∧ x ∈ W ∧ Function.Exact (u.app W) (v.app W)) : u ≫ v = 0 := by
  apply Scheme.Modules.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  intro s
  apply TopCat.Presheaf.IsSheaf.section_ext N.isSheaf
  intro x hx
  obtain ⟨W,hWV,hxW,hW⟩ := localExact V x hx
  refine ⟨W,hWV,hxW,?_⟩
  change N.val.map (homOfLE hWV).op ((u ≫ v).app V s) = N.val.map (homOfLE hWV).op 0
  rw [map_zero]
  exact (PresheafOfModules.naturality_apply (u ≫ v).val (homOfLE hWV).op s).symm.trans
    ((hW _).mpr ⟨_,rfl⟩)

theorem multiplyCubic_restrictCubic : multiplyCubic ≫ restrictCubic = 0 := by
  apply comp_zero_of_local_exact
  intro V x hx
  obtain ⟨i,W,hWV,hxW,hWi⟩ := neighborhood V x hx
  exact ⟨W.val,hWV,hxW,(localEquations i W hWi).2.1⟩

def cubicSequence := ShortComplex.mk multiplyCubic restrictCubic multiplyCubic_restrictCubic

theorem cubicSequence_shortExact : cubicSequence.ShortExact := by
  apply CycleQ2GeometricSheafLocalExactness.moduleSheaf_shortExact_of_neighborhoods X.ringCatSheaf cubicSequence
  intro V x hx
  obtain ⟨i,W,hWV,hxW,hWi⟩ := neighborhood V x hx
  exact ⟨W.val,hWV,hxW,localEquations i W hWi⟩

abbrev T := CycleQ2LiteralAmbientSmooth.IncidenceFiber 57
abbrev transport := Scheme.Modules.pushforward literalIso.hom
abbrev O3OnFiber := transport.obj O3
abbrev surfaceTwistOnFiber := (Scheme.Modules.pushforward CycleQ2LiteralAmbientSurface.surfaceToFiber).obj restrictedO3

private def cancelPush {A B : Scheme.{0}} (e : A ≅ B) :
    Scheme.Modules.pushforward e.hom ⋙ Scheme.Modules.pushforward e.inv ≅ 𝟭 _ :=
  Scheme.Modules.pushforwardComp _ _ ≪≫ Scheme.Modules.pushforwardCongr e.hom_inv_id ≪≫
    Scheme.Modules.pushforwardId A

private def transportedUnit : transport.obj (structureOn X) ≅ structureOn T := by
  let P := transport
  let Q := Scheme.Modules.pushforward literalIso.inv
  let F := Scheme.Modules.restrictFunctor literalIso.inv
  let e : P ≅ F := P.rightUnitor.symm ≪≫
    Functor.isoWhiskerLeft P (Scheme.Modules.restrictFunctorAdjCounitIso literalIso.inv).symm ≪≫
    (Functor.associator P Q F).symm ≪≫ Functor.isoWhiskerRight (cancelPush literalIso) F ≪≫ F.leftUnitor
  exact e.app (structureOn X) ≪≫ Scheme.Modules.restrictUnitIso literalIso.inv

private def transportedImage : transport.obj directImage ≅ surfaceTwistOnFiber :=
  (Scheme.Modules.pushforwardComp embedding literalIso.hom).app _ ≪≫
    (Scheme.Modules.pushforwardCongr (show embedding ≫ literalIso.hom = _ by rw [embedding_eq]; simp)).app _

private instance pushforwardAdditive {A B : Scheme.{0}} (u : A ⟶ B) :
    (Scheme.Modules.pushforward u).Additive where

private def pushEquivalence {A B : Scheme.{0}} (e : A ≅ B) : A.Modules ≌ B.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pushforward e.hom)
    (Scheme.Modules.pushforward e.inv) (cancelPush e).symm (cancelPush e.symm)

/-- The actual sequence on the incidence fiber, with the target explicitly
identified as a direct image along its original cubic surface inclusion. -/
def incidenceSequence : ShortComplex T.Modules :=
  ShortComplex.mk (transportedUnit.inv ≫ transport.map multiplyCubic)
    (transport.map restrictCubic ≫ transportedImage.hom) (by
      rw [Category.assoc, ← Category.assoc (transport.map multiplyCubic), ← Functor.map_comp,
        multiplyCubic_restrictCubic, Functor.map_zero, Limits.zero_comp, Limits.comp_zero])

theorem incidenceSequence_shortExact : incidenceSequence.ShortExact := by
  letI : transport.IsEquivalence := (pushEquivalence literalIso).isEquivalence_functor
  let C := cubicSequence.map transport
  have hC : C.ShortExact := cubicSequence_shortExact.map_of_exact _
  let e : C ≅ incidenceSequence := ShortComplex.isoMk transportedUnit (Iso.refl _) transportedImage
    (by simp [incidenceSequence,C,cubicSequence]) (by simp [incidenceSequence,C,cubicSequence])
  exact ShortComplex.shortExact_of_iso e hC

end CycleQ2LiteralAmbientCubicSequence
end

#print axioms CycleQ2LiteralAmbientCubicSequence.cubicSequence_shortExact
#print axioms CycleQ2LiteralAmbientCubicSequence.incidenceSequence_shortExact
