import Proposal.GeometricExteriorLocalFrames
import Proposal.GeometricAffineKahlerSheaf
import Proposal.GeometricLiteralResidueOneFrame
import Proposal.GeometricLiteralResidueVolume

/-!
# The volume frame of the sheafified exterior fourth power

The fourth exterior power of the actual differential sheaf is formed by
sheafifying the exterior powers of its sections. On the Jacobian chart
the coordinate differential basis trivializes these sectionwise powers
compatibly with restriction. The resulting sheaf isomorphism carries the
ordered differential wedge to the coordinate volume.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralResidueExteriorFrame

open CategoryTheory AlgebraicGeometry TopologicalSpace Opposite
open CycleQ2GeometricRegularDeRham CycleQ2LiteralResidueSheaf
open CycleQ2GeometricAffineDifferentialSheaf CycleQ2GeometricAffineKahlerSheaf
open CycleQ2GeometricExteriorSheaf CycleQ2LiteralResidueOneFrame
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricExteriorLocalFrames

abbrev Cotangent := affineDifferentialSheaf OpenRing

private def cotangentEquiv (U : Jacobian.Opens) :
    Cotangent.val.obj (op U) ≃ₗ[Γ(Jacobian, U)] OneSheaf.val.obj (op U) :=
  ((SheafOfModules.forget Jacobian.ringCatSheaf ⋙
    PresheafOfModules.evaluation Jacobian.ringCatSheaf.obj (op U)).mapIso
    (affineKahlerIso (A := OpenRing))).toLinearEquiv

def cotangentBasis (U : Jacobian.Opens) :
    Module.Basis (Fin 4) Γ(Jacobian, U) (Cotangent.val.obj (op U)) :=
  (sectionBasis U).map (cotangentEquiv U).symm

theorem cotangentBasis_restrict {U V : Jacobian.Opens} (h : V ⟶ U) (i : Fin 4) :
    Cotangent.val.map h.op (cotangentBasis U i) = cotangentBasis V i := by
  change Cotangent.val.map h.op ((affineKahlerIso (A := OpenRing)).inv.val.app _ (sectionBasis U i)) =
    (affineKahlerIso (A := OpenRing)).inv.val.app _ (sectionBasis V i)
  rw [← PresheafOfModules.naturality_apply]
  exact congrArg ((affineKahlerIso (A := OpenRing)).inv.val.app (op V)) (sectionBasis_restrict h i)

/-- The frame vectors are the universal differentials of the four original coordinates. -/
theorem cotangentBasis_eq_D (U : Jacobian.Opens) (i : Fin 4) :
    cotangentBasis U i = (affineUniversalDifferential OpenRing).d (X := op U)
      (algebraMap OpenRing (CycleQ2GeometricAffineDerivations.AffineSections (A := OpenRing) U)
        (polynomialValue (MvPolynomial.X i.succ))) := by
  apply (cotangentEquiv U).injective
  change cotangentEquiv U ((cotangentEquiv U).symm (sectionBasis U i)) =
    (differentialToTilde (A := OpenRing)).val.app _ _
  rw [LinearEquiv.apply_symm_apply, sectionBasis_apply, differentialToTilde_D,
    tildeDerivation_algebraMap]
  exact congrArg (tilde.toOpen (R := CommRingCat.of OpenRing) OneModule U)
    (CycleQ2GeometricAffineScheme.coordinateBasis_apply i)

private theorem basis_top_wedge {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis (Fin 4) R M) :
    b.exteriorPower 4 CycleQ2AffineExterior.topIndex = exteriorPower.ιMulti R 4 b := by
  rw [exteriorPower.basis_apply]
  unfold exteriorPower.ιMulti_family
  congr 1
  funext i
  have h : (fun j : Fin 4 => j) = (Finset.univ : Finset (Fin 4)).orderEmbOfFin (by simp) :=
    Finset.orderEmbOfFin_unique _ (fun _ => Finset.mem_univ _) strictMono_id
  exact congrArg b (congrFun h i).symm

private theorem fourthCoordinate_wedge {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis (Fin 4) R M) :
    fourthCoordinates b (exteriorPower.ιMulti R 4 b) = 1 := by
  rw [← basis_top_wedge]
  change (b.exteriorPower 4).coord CycleQ2AffineExterior.topIndex
    (b.exteriorPower 4 CycleQ2AffineExterior.topIndex) = 1
  simp [Module.Basis.coord_apply]

private theorem fourthCoordinate_map {R S M N : Type} [CommRing R] [CommRing S]
    [AddCommGroup M] [AddCommGroup N] [Module R M] [Module S N]
    (φ : R →+* S) (f : M →ₛₗ[φ] N) (b : Module.Basis (Fin 4) R M)
    (c : Module.Basis (Fin 4) S N) (h : ∀ i, f (b i) = c i) (ω : ⋀[R]^4 M) :
    fourthCoordinates c (exteriorMap φ f 4 ω) = φ (fourthCoordinates b ω) := by
  have hω : fourthCoordinates b ω • exteriorPower.ιMulti R 4 b = ω := by
    apply (fourthCoordinates b).injective
    rw [map_smul, fourthCoordinate_wedge, smul_eq_mul, mul_one]
  calc
    _ = fourthCoordinates c (exteriorMap φ f 4
        (fourthCoordinates b ω • exteriorPower.ιMulti R 4 b)) :=
      congrArg (fun z => fourthCoordinates c (exteriorMap φ f 4 z)) hω.symm
    _ = fourthCoordinates c (φ (fourthCoordinates b ω) • exteriorPower.ιMulti S 4 c) := by
      rw [map_smulₛₗ, exteriorMap_wedge]
      exact congrArg (fun v : Fin 4 → N => fourthCoordinates c
        (φ (fourthCoordinates b ω) • exteriorPower.ιMulti S 4 v)) (funext h)
    _ = _ := by rw [map_smul, fourthCoordinate_wedge, smul_eq_mul, mul_one]

section Frame
variable {T : TopCat.{0}} (R : T.Sheaf CommRingCat.{0})
    (M : PresheafOfModules.{0} (ringSheaf R).obj)
    (B : ∀ U : Opens T, Module.Basis (Fin 4) (R.obj.obj (op U)) (M.obj (op U)))
    (hB : ∀ {U V : Opens T} (h : V ⟶ U) (i : Fin 4), M.map h.op (B U i) = B V i)

private def exteriorPresheafIso :
    exteriorPresheaf R.obj M 4 ≅ (SheafOfModules.unit (ringSheaf R)).val :=
  PresheafOfModules.isoMk (fun U => (fourthCoordinates (B U.unop)).toModuleIso) (by
    intro U V h
    apply ConcreteCategory.hom_ext
    intro ω
    exact fourthCoordinate_map (R.obj.map h).hom (M.restrictₛₗ h) _ _ (hB h.unop) ω)

private def sheafVolumeIso : exteriorSheaf R M 4 ≅ SheafOfModules.unit (ringSheaf R) :=
  @CycleQ2LocalSheafificationFrame.isoOfPresentation (Opens T) _ (Opens.grothendieckTopology T)
    (ringSheaf R) (exteriorPresheaf R.obj M 4) (exteriorSheaf R M 4)
    (SheafOfModules.unit (ringSheaf R)) (toExteriorSheaf R M 4) _
    (exteriorPresentation_locallyInjective R M 4) (exteriorPresentation_locallySurjective R M 4)
    (exteriorPresheafIso R M B hB)

private theorem sheafVolumeIso_wedge (U : Opens T) :
    (sheafVolumeIso R M B hB).hom.val.app (op U)
      (wedgeSection R M 4 U (B U)) = (1 : R.obj.obj (op U)) :=
  (@CycleQ2LocalSheafificationFrame.isoOfPresentation_hom (Opens T) _ (Opens.grothendieckTopology T)
    (ringSheaf R) (exteriorPresheaf R.obj M 4) (exteriorSheaf R M 4)
    (SheafOfModules.unit (ringSheaf R)) (toExteriorSheaf R M 4) _
    (exteriorPresentation_locallyInjective R M 4) (exteriorPresentation_locallySurjective R M 4)
    (exteriorPresheafIso R M B hB) (op U) _).trans (fourthCoordinate_wedge (B U))

end Frame

abbrev actualFourth := exteriorSheaf Jacobian.sheaf Cotangent.val 4

def actualVolumeIso : actualFourth ≅ structureModule :=
  sheafVolumeIso Jacobian.sheaf Cotangent.val cotangentBasis cotangentBasis_restrict

def associatedFourthIso : actualFourth ≅ fourForms := actualVolumeIso ≪≫ volumeIso.symm

theorem actualVolumeIso_wedge (U : Jacobian.Opens) :
    actualVolumeIso.hom.val.app (op U)
      (wedgeSection Jacobian.sheaf Cotangent.val 4 U (cotangentBasis U)) = (1 : Γ(Jacobian, U)) :=
  sheafVolumeIso_wedge Jacobian.sheaf Cotangent.val cotangentBasis cotangentBasis_restrict U

/-- The comparison on the ordered wedge gives the original algebraic chart volume. -/
theorem associatedFourthIso_wedge (U : Jacobian.Opens) :
    associatedFourthIso.hom.val.app (op U)
      (wedgeSection Jacobian.sheaf Cotangent.val 4 U (cotangentBasis U)) =
        fourthSection U chartVolume := by
  apply ((SheafOfModules.forget Jacobian.ringCatSheaf ⋙
    PresheafOfModules.evaluation Jacobian.ringCatSheaf.obj (op U)).mapIso volumeIso).toLinearEquiv.injective
  change volumeIso.hom.val.app _ (volumeIso.inv.val.app _ (actualVolumeIso.hom.val.app _
    (wedgeSection Jacobian.sheaf Cotangent.val 4 U (cotangentBasis U)))) =
      volumeIso.hom.val.app _ (fourthSection U chartVolume)
  rw [volumeIso_hom_inv, actualVolumeIso_wedge, volumeIso_toOpen, chartVolumeCoordinate_chartVolume,
    map_one]

abbrev actualAdditiveFourth := (SheafOfModules.toSheaf Jacobian.ringCatSheaf).obj actualFourth

def actualExteriorDifferential : additiveForms ⟶ actualAdditiveFourth :=
  topDifferential ≫ (SheafOfModules.toSheaf Jacobian.ringCatSheaf).map actualVolumeIso.inv

def actualProtectedSection (U : Jacobian.Opens) : actualAdditiveFourth.obj.obj (op U) :=
  (show Γ(Jacobian, U) from protectedSection U) •
    wedgeSection Jacobian.sheaf Cotangent.val 4 U (cotangentBasis U)

theorem actualVolumeIso_protected (U : Jacobian.Opens) :
    actualVolumeIso.hom.val.app (op U) (actualProtectedSection U) = protectedSection U := by
  change (actualVolumeIso.hom.val.app (op U)).hom (_ • _) = _
  rw [map_smul, actualVolumeIso_wedge]
  exact mul_one (show Γ(Jacobian, U) from protectedSection U)

theorem actualExteriorBoundary_iff (U : Jacobian.Opens) (w : additiveForms.obj.obj (op U)) :
    actualExteriorDifferential.hom.app (op U) w = actualProtectedSection U ↔
      topDifferential.hom.app (op U) w = protectedSection U := by
  have hi := ((SheafOfModules.forget Jacobian.ringCatSheaf ⋙
    PresheafOfModules.evaluation Jacobian.ringCatSheaf.obj (op U)).mapIso actualVolumeIso).toLinearEquiv.injective
  change actualVolumeIso.inv.val.app _ (topDifferential.hom.app _ w) = _ ↔ _
  have hcancel (x : structureModule.val.obj (op U)) :
      actualVolumeIso.hom.val.app (op U) (actualVolumeIso.inv.val.app (op U) x) = x :=
    congrArg (fun f : structureModule ⟶ structureModule => f.val.app (op U) x) actualVolumeIso.inv_hom_id
  constructor
  · intro hw
    simpa only [hcancel, actualVolumeIso_protected] using congrArg (actualVolumeIso.hom.val.app (op U)) hw
  · intro hw
    apply hi
    change actualVolumeIso.hom.val.app (op U) (actualVolumeIso.inv.val.app _ _) =
      actualVolumeIso.hom.val.app (op U) (actualProtectedSection U)
    rw [hcancel, actualVolumeIso_protected, hw]

end CycleQ2LiteralResidueExteriorFrame
end

#print axioms CycleQ2LiteralResidueExteriorFrame.associatedFourthIso
#print axioms CycleQ2LiteralResidueExteriorFrame.cotangentBasis_eq_D
#print axioms CycleQ2LiteralResidueExteriorFrame.associatedFourthIso_wedge
#print axioms CycleQ2LiteralResidueExteriorFrame.actualExteriorBoundary_iff
