import Proposal.GeometricLiteralResidueExteriorFrame
import Proposal.GeometricPrincipalRestriction

/-!
# The intrinsic third exterior sheaf on the Jacobian chart

The four ordered triple wedges form a frame on each open. Restriction sends
each wedge to the corresponding wedge on the smaller open, so the
sheafification agrees with the associated sheaf of the algebraic third
exterior module. The differential and the protected boundary equation
therefore have an intrinsic source as well as an intrinsic target.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralResidueExteriorFrame

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricRegularDeRham CycleQ2LiteralResidueSheaf CycleQ2LiteralResidueOneFrame
open CycleQ2GeometricExteriorSheaf CycleQ2GeometricExteriorLocalFrames
open scoped KaehlerDifferential

private def tripleBasis {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis (Fin 4) R M) : Module.Basis (Fin 4) R (⋀[R]^3 M) :=
  (b.exteriorPower 3).reindex CycleQ2AffineExterior.omitEquiv.symm

private theorem tripleBasis_wedge {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis (Fin 4) R M) (i : Fin 4) :
    tripleBasis b i = exteriorPower.ιMulti R 3 (i.removeNth b) := by
  rw [tripleBasis, Module.Basis.reindex_apply, Equiv.symm_symm]
  change b.exteriorPower 3 (CycleQ2AffineExterior.omitIndex i) = _
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext j
  simp only [Function.comp_apply, Set.powersetCard.ofFinEmbEquiv_symm_apply,
    CycleQ2AffineExterior.omitIndex, Finset.orderEmbOfFin_compl_singleton_eq_succAboveOrderEmb,
    Fin.removeNth]
  rfl

private abbrev ThirdModule : ModuleCat (CommRingCat.of OpenRing) := ModuleCat.of OpenRing Third

private def coefficientEquiv :=
  CycleQ2GeometricAffineScheme.coordinateBasis.equiv thirdFrame (Equiv.refl _)

private def coefficientHom : OneModule ⟶ ThirdModule := ModuleCat.ofHom coefficientEquiv.toLinearMap

private def coefficientIso : OneModule ≅ ThirdModule where
  hom := coefficientHom
  inv := ModuleCat.ofHom coefficientEquiv.symm.toLinearMap
  hom_inv_id := by
    apply ConcreteCategory.hom_ext
    intro x
    exact coefficientEquiv.symm_apply_apply x
  inv_hom_id := by
    apply ConcreteCategory.hom_ext
    intro x
    exact coefficientEquiv.apply_symm_apply x

private def frameIso : OneSheaf ≅ threeForms :=
  (tilde.functor (CommRingCat.of OpenRing)).mapIso coefficientIso

private def tildeBasis (U : Jacobian.Opens) :
    Module.Basis (Fin 4) Γ(Jacobian, U) (threeForms.val.obj (op U)) :=
  (sectionBasis U).map (((SheafOfModules.forget Jacobian.ringCatSheaf ⋙
    PresheafOfModules.evaluation Jacobian.ringCatSheaf.obj (op U)).mapIso frameIso).toLinearEquiv)

private theorem tildeBasis_frameSection (U : Jacobian.Opens) (i : Fin 4) :
    tildeBasis U i = frameSection U i := by
  change frameIso.hom.val.app (op U) (sectionBasis U i) = _
  rw [sectionBasis_apply]
  let b := CycleQ2GeometricAffineScheme.coordinateBasis
  have h := ConcreteCategory.congr_hom (C := ModuleCat (CommRingCat.of OpenRing))
    (tilde.toOpen_map_app (R := CommRingCat.of OpenRing) coefficientHom U) (b i)
  change _ = tilde.toOpen ThirdModule U (coefficientEquiv (b i)) at h
  rw [show coefficientEquiv (b i) = thirdFrame i by
    simp only [coefficientEquiv, Module.Basis.equiv_apply, Equiv.refl_apply, b]] at h
  exact h

private theorem tildeBasis_restrict {U V : Jacobian.Opens} (h : V ⟶ U) (i : Fin 4) :
    threeForms.val.map h.op (tildeBasis U i) = tildeBasis V i := by
  rw [tildeBasis_frameSection, tildeBasis_frameSection]
  rfl

section Naturality

variable {R S M N P Q : Type} [CommRing R] [CommRing S]
  [AddCommGroup M] [AddCommGroup N] [AddCommGroup P] [AddCommGroup Q]
  [Module R M] [Module S N] [Module R P] [Module S Q]
  (φ : R →+* S) (f : M →ₛₗ[φ] N)
  (b : Module.Basis (Fin 4) R M) (c : Module.Basis (Fin 4) S N)
  (hb : ∀ i, f (b i) = c i)

include hb

private theorem tripleBasis_map (i : Fin 4) :
    exteriorMap φ f 3 (tripleBasis b i) = tripleBasis c i := by
  rw [tripleBasis_wedge, tripleBasis_wedge, exteriorMap_wedge]
  exact congrArg (exteriorPower.ιMulti S 3) (funext fun j => hb (i.succAbove j))

private theorem tripleEquiv_map (g : P →ₛₗ[φ] Q)
    (p : Module.Basis (Fin 4) R P) (q : Module.Basis (Fin 4) S Q)
    (hp : ∀ i, g (p i) = q i) (ω : ⋀[R]^3 M) :
    (tripleBasis c).equiv q (Equiv.refl _) (exteriorMap φ f 3 ω) =
      g ((tripleBasis b).equiv p (Equiv.refl _) ω) := by
  have hh : ((tripleBasis c).equiv q (Equiv.refl _)).toLinearMap.comp (exteriorMap φ f 3) =
      g.comp ((tripleBasis b).equiv p (Equiv.refl _)).toLinearMap := by
    apply (tripleBasis b).ext
    intro i
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, tripleBasis_map φ f b c hb,
      Module.Basis.equiv_apply, Equiv.refl_apply, hp]
  exact LinearMap.congr_fun hh ω

end Naturality

section FramedSheaves

open CycleQ2GeometricDifferentialSheaf
variable {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
    (M : PresheafOfModules.{0} (ringSheaf R).obj)
    (N : SheafOfModules.{0} (ringSheaf R))
    (b : ∀ U : Opens T, Module.Basis (Fin 4) (R.obj.obj (op U)) (M.obj (op U)))
    (p : ∀ U : Opens T, Module.Basis (Fin 4) (R.obj.obj (op U)) (N.val.obj (op U)))
    (hb : ∀ {U V : Opens T} (h : V ⟶ U) i, M.map h.op (b U i) = b V i)
    (hp : ∀ {U V : Opens T} (h : V ⟶ U) i, N.val.map h.op (p U i) = p V i)

include hb hp

private def thirdPresentationIso :
    exteriorPresheaf R.obj M 3 ≅ N.val :=
  PresheafOfModules.isoMk (fun U => ((tripleBasis (b U.unop)).equiv (p U.unop) (Equiv.refl _)).toModuleIso) (by
    intro U V h
    apply ConcreteCategory.hom_ext
    intro ω
    exact tripleEquiv_map (R.obj.map h).hom (M.restrictₛₗ h) _ _ (hb h.unop)
      (N.val.restrictₛₗ h) _ _ (hp h.unop) ω)

private def sheafTripleIso : exteriorSheaf R M 3 ≅ N :=
  @CycleQ2LocalSheafificationFrame.isoOfPresentation (Opens T) _ (Opens.grothendieckTopology T)
    (ringSheaf R) (exteriorPresheaf R.obj M 3) (exteriorSheaf R M 3) N
    (toExteriorSheaf R M 3) _ (exteriorPresentation_locallyInjective R M 3)
    (exteriorPresentation_locallySurjective R M 3) (thirdPresentationIso R M N b p hb hp)

private theorem sheafTripleIso_wedge (U : Opens T) (i : Fin 4) :
    (sheafTripleIso R M N b p hb hp).hom.val.app (op U)
      (wedgeSection R M 3 U (i.removeNth (b U))) = p U i := by
  have h := @CycleQ2LocalSheafificationFrame.isoOfPresentation_hom (Opens T) _
    (Opens.grothendieckTopology T) (ringSheaf R) (exteriorPresheaf R.obj M 3)
    (exteriorSheaf R M 3) N (toExteriorSheaf R M 3) _
    (exteriorPresentation_locallyInjective R M 3) (exteriorPresentation_locallySurjective R M 3)
    (thirdPresentationIso R M N b p hb hp) (op U) (tripleBasis (b U) i)
  change (sheafTripleIso R M N b p hb hp).hom.val.app (op U) (exteriorSection R M 3 U
    (tripleBasis (b U) i)) = (tripleBasis (b U)).equiv (p U) (Equiv.refl _) (tripleBasis (b U) i) at h
  rw [Module.Basis.equiv_apply, Equiv.refl_apply, tripleBasis_wedge] at h
  exact h

end FramedSheaves

abbrev actualThird := exteriorSheaf Jacobian.sheaf Cotangent.val 3

def associatedThirdIso : actualThird ≅ threeForms :=
  sheafTripleIso Jacobian.sheaf Cotangent.val threeForms cotangentBasis tildeBasis
    cotangentBasis_restrict tildeBasis_restrict

theorem associatedThirdIso_wedge (U : Jacobian.Opens) (i : Fin 4) :
    associatedThirdIso.hom.val.app (op U)
      (wedgeSection Jacobian.sheaf Cotangent.val 3 U (i.removeNth (cotangentBasis U))) =
        frameSection U i :=
  (sheafTripleIso_wedge Jacobian.sheaf Cotangent.val threeForms cotangentBasis tildeBasis
    cotangentBasis_restrict tildeBasis_restrict U i).trans (tildeBasis_frameSection U i)

abbrev actualAdditiveThird := (SheafOfModules.toSheaf Jacobian.ringCatSheaf).obj actualThird

/-- The top differential as a map between the intrinsic third and fourth exterior sheaves. -/
def intrinsicExteriorDifferential : actualAdditiveThird ⟶ actualAdditiveFourth :=
  (SheafOfModules.toSheaf Jacobian.ringCatSheaf).map associatedThirdIso.hom ≫ actualExteriorDifferential

theorem intrinsic_boundary_iff (U : Jacobian.Opens) :
    (∃ w : actualAdditiveThird.obj.obj (op U),
      intrinsicExteriorDifferential.hom.app (op U) w = actualProtectedSection U) ↔
    ∃ w : additiveForms.obj.obj (op U),
      topDifferential.hom.app (op U) w = protectedSection U := by
  constructor
  · rintro ⟨w, hw⟩
    exact ⟨associatedThirdIso.hom.val.app (op U) w, (actualExteriorBoundary_iff U _).mp hw⟩
  · rintro ⟨w, hw⟩
    refine ⟨associatedThirdIso.inv.val.app (op U) w, ?_⟩
    have h : associatedThirdIso.hom.val.app (op U) (associatedThirdIso.inv.val.app (op U) w) = w :=
      congrArg (fun f : threeForms ⟶ threeForms => f.val.app (op U) w) associatedThirdIso.inv_hom_id
    change actualExteriorDifferential.hom.app _ (associatedThirdIso.hom.val.app _
      (associatedThirdIso.inv.val.app _ w)) = _
    rw [h]
    exact (actualExteriorBoundary_iff U w).mpr hw

/-- A rational primitive exists precisely when the protected intrinsic four-form is a boundary
over a nonempty principal open of the original chart. -/
theorem rationalPrimitive_iff_intrinsicBoundary :
    (∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA) ↔
      ∃ s : OpenRing, s ≠ 0 ∧ ∃ w : actualAdditiveThird.obj.obj (op (PrimeSpectrum.basicOpen s)),
        intrinsicExteriorDifferential.hom.app _ w = actualProtectedSection _ := by
  rw [CycleQ2GeometricRationalSpread.protected_exact_iff_exists_regular_zero]
  apply exists_congr
  intro s
  exact and_congr_right fun hs => (classOf_eq_zero_iff s _).trans
    ((principal_exact_iff s hs).symm.trans (intrinsic_boundary_iff _).symm)

end CycleQ2LiteralResidueExteriorFrame
end

#print axioms CycleQ2LiteralResidueExteriorFrame.associatedThirdIso_wedge
#print axioms CycleQ2LiteralResidueExteriorFrame.intrinsicExteriorDifferential

#print axioms CycleQ2LiteralResidueExteriorFrame.rationalPrimitive_iff_intrinsicBoundary
