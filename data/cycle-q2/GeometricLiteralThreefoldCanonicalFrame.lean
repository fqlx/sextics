import Proposal.GeometricLiteralThreefoldCanonicalVolume
import Proposal.GeometricLiteralThreefoldGradientAtlas
import Proposal.GeometricLiteralThreefoldDifferentialFrame

/-!
# The canonical bundle of the original fixed sextic threefold

The actual projective residue restricts on each of the sixteen gradient opens
to the oriented hypersurface residue. Its determinant coordinate is a unit.
Uniqueness and descent of the scalar coefficients give a frame on every open
of the fixed incidence fiber.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 1200000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2LiteralThreefoldCanonicalFrame

open CategoryTheory Opposite AlgebraicGeometry
  CycleQ2LiteralAbelJacobiContraction CycleQ2LiteralAmbientCharts
  CycleQ2LiteralThreefoldGradientAtlas CycleQ2LiteralThreefoldCanonicalVolume
  CycleQ2LiteralThreefoldChartVolume CycleQ2LiteralThreefoldResidueFrame
  CycleQ2LiteralThreefoldResidueMinors CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricAffineChartSections CycleQ2ChartExteriorBinding CycleQ2ExteriorSectionNaturality
  CycleQ2LiteralThreefoldDifferentialFrame CycleQ2ExteriorTopBaseChange

private abbrev patchMap (i j : Fin 4) := IsScalarTower.toAlgHom ℂ (T i) (Patch i j)

theorem gradientOverComplex (i j : Fin 4) :
    (gradientIso i j).inv ≫ (gOpen i j).ι ≫ structural =
      Spec.map (CommRingCat.ofHom (algebraMap ℂ (Patch i j))) := by
  rw [← Category.assoc, gradientIso_inv_ι, Category.assoc]
  change _ ≫ chartInclusion i ≫ CycleQ2LiteralAmbientSmooth.incidenceFiberToComplex 57 = _
  rw [chartInclusion_overComplex, ← Spec.map_comp]
  apply congrArg Spec.map
  exact CommRingCat.hom_ext (RingHom.ext (patchMap i j).commutes)

private abbrev oriented (i j : Fin 4) := (-1 : Patch i j)^i.val • patchResidue i j

theorem volume_restrict_gradient (i j : Fin 4) (V : Over (gOpen i j)) :
    threeForms.val.map (homOfLE (le_top : V.left ≤ ⊤)).op volume =
      chartExteriorSheafSection (gradientIso i j) structural (gradientOverComplex i j)
        3 V (oriented i j) := by
  refine (volume_restrict_subopen i V.left (V.hom.le.trans (gOpen_le i j))).trans ?_
  have hh := chartExteriorSheafSection_differentialMap (fixedChart i).symm (gradientIso i j)
    (gOpen_le i j) structural (chartOverComplex i) (gradientOverComplex i j)
    (patchMap i j) (gradientIso_inv_ι i j) V 3 ((-1 : T i)^i.val • chartVolume i)
  refine hh.symm.trans (congrArg (chartExteriorSheafSection (gradientIso i j) structural
    (gradientOverComplex i j) 3 V) ?_)
  rw [map_smulₛₗ, RingHom.map_pow, map_neg, map_one, chartVolume_on_patch]

private theorem orientation_coordinate_isUnit (i j : Fin 4) :
    IsUnit (topCoordinate (basis i j) (oriented i j)) := by
  have ⟨c, hc, _⟩ := patchResidue_frame i j (exteriorPower.ιMulti _ 3 (basis i j))
  have h := congrArg (topCoordinate (basis i j)) hc
  rw [map_smul, smul_eq_mul, topCoordinate_basis] at h
  change IsUnit (topCoordinate _ ((-1 : Patch i j)^i.val • patchResidue i j))
  rw [map_smul, smul_eq_mul]
  exact ((isUnit_one.neg : IsUnit (-1 : Patch i j)).pow _).mul (isUnit_iff_exists_inv.mpr ⟨c, (mul_comm _ _).trans h⟩)

def gradientFrame (i j : Fin 4) :
    threeForms.over (gOpen i j) ≅ SheafOfModules.unit ((ringSheaf X.sheaf).over (gOpen i j)) :=
  frameIso (gradientIso i j) structural (gradientOverComplex i j) (basis i j)

theorem frame_coordinate_isUnit (i j : Fin 4) (V : Over (gOpen i j)) :
    IsUnit (show Γ(X,V.left) from (gradientFrame i j).hom.val.app (op V)
      (threeForms.val.map (homOfLE (le_top : V.left ≤ ⊤)).op volume)) := by
  rw [volume_restrict_gradient, gradientFrame, frameIso_on_section]
  exact (orientation_coordinate_isUnit i j).map (chartSection (gradientIso i j) V)

private theorem smul_bijective_of_unit_coordinate {R M : Type} [CommRing R] [AddCommGroup M]
    [Module R M] (E : M ≃ₗ[R] R) (y : M) (hy : IsUnit (E y)) :
    Function.Bijective (fun c : R => c • y) := by
  let u := hy.unit
  let J := (LinearEquiv.smulOfUnit u : R ≃ₗ[R] R).trans E.symm
  have hJ : (J : R → M) = fun c => c • y := by
    funext c
    apply E.injective
    change E (E.symm ((u : R) * c)) = E (c • y)
    rw [LinearEquiv.apply_symm_apply, map_smul, smul_eq_mul, hy.unit_spec, mul_comm]
  exact hJ ▸ J.bijective

theorem volume_frame_on_gradient (i j : Fin 4) (V : Over (gOpen i j)) :
    Function.Bijective (fun c : Γ(X,V.left) =>
      c • threeForms.val.map (homOfLE (le_top : V.left ≤ ⊤)).op volume) := by
  apply smul_bijective_of_unit_coordinate (R := Γ(X,V.left)) (M := threeForms.val.obj (op V.left))
    (((SheafOfModules.evaluation ((ringSheaf X.sheaf).over (gOpen i j)) (op V)).mapIso
      (gradientFrame i j)).toLinearEquiv) _
  exact frame_coordinate_isUnit i j V

private abbrev sub (U : X.Opens) (s : Fin 4 × Fin 4) := U ⊓ gOpen s.1 s.2

private theorem sub_cover (U : X.Opens) : U ≤ ⨆ a, sub U a := by
  change U ≤ ⨆ a : Fin 4 × Fin 4, U ⊓ gOpen a.1 a.2
  rw [← inf_iSup_eq, iSup_prod, gOpen_cover, inf_top_eq]

private abbrev r {O P : X.Opens} (h : P ≤ O) (x : Γ(X,O)) := X.presheaf.map (homOfLE h).op x
private abbrev m {O P : X.Opens} (h : P ≤ O) (x : threeForms.val.obj (op O)) := threeForms.val.map (homOfLE h).op x
private abbrev generate (O : X.Opens) (x : Γ(X,O)) := x • m (le_top : O ≤ ⊤) volume
private theorem m_comp {O P Q : X.Opens} (hPQ : Q ≤ P) (hOP : P ≤ O) (y : threeForms.val.obj (op O)) :
    m hPQ (m hOP y) = m (hPQ.trans hOP) y := (threeForms.val.map_comp_apply _ _ y).symm

private theorem generate_res {O P : X.Opens} (h : P ≤ O) (x : Γ(X,O)) :
    m h (generate O x) = generate P (r h x) := by
  unfold generate
  rw [m, threeForms.val.map_smul]
  change _ • m h (m _ volume) = _
  rw [m_comp]
  rfl

private theorem generated_restriction {O P Q : X.Opens} (h : P ≤ O) (k : Q ≤ P)
    (x : Γ(X,P)) (y : threeForms.val.obj (op O)) (e : generate P x = m h y) :
    generate Q (r k x) = m (k.trans h) y :=
  (generate_res k x).symm.trans ((congrArg (m k) e).trans (m_comp k h y))

private theorem generate_inj (O : X.Opens) : Function.Injective (generate O) := by
  intro x y hxy
  apply X.sheaf.eq_of_locally_eq' (sub O) O (fun _ => homOfLE inf_le_left) (sub_cover O) x y
  intro a
  apply (volume_frame_on_gradient a.1 a.2 (Over.mk (homOfLE
    (show sub O a ≤ gOpen a.1 a.2 from inf_le_right)))).injective
  exact (generate_res (show sub O a ≤ O from inf_le_left) x).symm.trans
    ((congrArg (m (show sub O a ≤ O from inf_le_left)) hxy).trans (generate_res inf_le_left y))

/-- The global residue generates all genuine three-form sections on every open. -/
theorem volume_frame (O : X.Opens) : Function.Bijective (fun c : Γ(X,O) =>
    c • threeForms.val.map (homOfLE (le_top : O ≤ ⊤)).op volume) := by
  refine ⟨generate_inj O, ?_⟩
  intro y
  choose s hs using fun a : Fin 4 × Fin 4 => (volume_frame_on_gradient a.1 a.2
    (Over.mk (homOfLE (show sub O a ≤ gOpen a.1 a.2 from inf_le_right)))).surjective
      (m (show sub O a ≤ O from inf_le_left) y)
  have hc (a b : Fin 4 × Fin 4) :
      r (show sub O a ⊓ sub O b ≤ sub O a from inf_le_left) (s a) = r inf_le_right (s b) := by
    apply generate_inj _
    have ha := generated_restriction (show sub O a ≤ O from inf_le_left)
      (show sub O a ⊓ sub O b ≤ sub O a from inf_le_left) (s a) y (hs a)
    have hb := generated_restriction (show sub O b ≤ O from inf_le_left)
      (show sub O a ⊓ sub O b ≤ sub O b from inf_le_right) (s b) y (hs b)
    exact ha.trans hb.symm
  obtain ⟨x, hx, _⟩ := X.sheaf.existsUnique_gluing' (sub O) O (fun _ => homOfLE inf_le_left) (sub_cover O) s hc
  refine ⟨x, ?_⟩
  let F : TopCat.Sheaf AddCommGrpCat X := (SheafOfModules.toSheaf (ringSheaf X.sheaf)).obj threeForms
  apply F.eq_of_locally_eq' (sub O) O (fun _ => homOfLE inf_le_left) (sub_cover O)
  intro a
  change m (show sub O a ≤ O from inf_le_left) (generate O x) = m inf_le_left y
  exact (generate_res (show sub O a ≤ O from inf_le_left) x).trans
    ((congrArg (generate (sub O a)) (hx a)).trans (hs a))

/-- Multiplication by the residue identifies the scalar sections with all three-forms. -/
def volumeEquiv (O : X.Opens) : Γ(X,O) ≃ₗ[Γ(X,O)] threeForms.val.obj (op O) :=
  LinearEquiv.ofBijective (LinearMap.toSpanSingleton (Γ(X,O)) _
    (threeForms.val.map (homOfLE (le_top : O ≤ ⊤)).op volume)) (volume_frame O)

private def volumeMorphism : SheafOfModules.unit (ringSheaf X.sheaf) ⟶ threeForms :=
  threeForms.unitHomEquiv.symm (threeForms.val.sectionsMk
    (fun U => threeForms.val.map (homOfLE (le_top : U.unop ≤ ⊤)).op volume)
    (fun _ _ _ => by rw [← threeForms.val.map_comp_apply]; congr 2))

/-- The global section trivializes the canonical sheaf of the original fixed threefold. -/
def volumeIso : SheafOfModules.unit (ringSheaf X.sheaf) ≅ threeForms := by
  letI (U : X.Opensᵒᵖ) : IsIso (volumeMorphism.val.app U) :=
    (ConcreteCategory.isIso_iff_bijective _).mpr (volume_frame U.unop)
  exact (SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun U => asIso (volumeMorphism.val.app U))
      (fun {_ _} f => volumeMorphism.val.naturality f))

theorem volumeIso_hom_apply (U : X.Opens) (c : Γ(X,U)) :
    volumeIso.hom.val.app (op U) c =
      c • threeForms.val.map (homOfLE (le_top : U ≤ ⊤)).op volume := rfl

end CycleQ2LiteralThreefoldCanonicalFrame
end

#print axioms CycleQ2LiteralThreefoldCanonicalFrame.volume_restrict_gradient
#print axioms CycleQ2LiteralThreefoldCanonicalFrame.volumeEquiv
#print axioms CycleQ2LiteralThreefoldCanonicalFrame.volumeIso_hom_apply
