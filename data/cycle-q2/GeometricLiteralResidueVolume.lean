import Proposal.GeometricLiteralResidueDifferential

/-!
# The protected differential with values in the fourth exterior power

The ordered coordinate volume trivializes the sheaf associated to the fourth
exterior power of the Kähler module on the Jacobian chart. In this frame the
literal top differential specializes on every nonempty principal open to the
regular exterior differential, and the protected section specializes to its
prescribed residue form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralResidueSheaf

open AlgebraicGeometry CategoryTheory Opposite
open CycleQ2GeometricRegularDeRham CycleQ2GeometricAffineDerivations
open CycleQ2LiteralResidueBasicChart CycleQ2AffineClearing
open scoped KaehlerDifferential

abbrev Fourth := ⋀[OpenRing]^4 Ω[OpenRing⁄ℂ]

abbrev FourthModule : ModuleCat (CommRingCat.of OpenRing) := ModuleCat.of OpenRing Fourth

abbrev fourForms := tilde (R := CommRingCat.of OpenRing) FourthModule

abbrev additiveFourForms := (SheafOfModules.toSheaf Jacobian.ringCatSheaf).obj fourForms

def fourthCoordinates {R M : Type} [CommRing R] [AddCommGroup M] [Module R M]
    (b : Module.Basis (Fin 4) R M) : (⋀[R]^4 M) ≃ₗ[R] R := by
  classical
  let B := b.exteriorPower 4
  let j := CycleQ2AffineExterior.topIndex
  refine { B.coord j with
    invFun := fun a => a • B j
    left_inv := ?_
    right_inv := ?_ }
  · intro η
    apply B.repr.injective
    ext i
    rw [CycleQ2AffineExterior.topIndex_unique i]
    simp [B, j, Module.Basis.coord_apply, Finsupp.smul_apply]
  · intro a
    simp [B, j, Module.Basis.coord_apply]

def chartVolume : Fourth :=
  CycleQ2GeometricAffineScheme.coordinateBasis.exteriorPower 4 CycleQ2AffineExterior.topIndex

def chartVolumeCoordinate : Fourth ≃ₗ[OpenRing] OpenRing :=
  fourthCoordinates CycleQ2GeometricAffineScheme.coordinateBasis

@[simp] theorem chartVolumeCoordinate_chartVolume : chartVolumeCoordinate chartVolume = 1 := by
  change (CycleQ2GeometricAffineScheme.coordinateBasis.exteriorPower 4).coord
    CycleQ2AffineExterior.topIndex chartVolume = 1
  simp [chartVolume, Module.Basis.coord_apply]

private def coefficientHom : FourthModule ⟶ ModuleCat.of (CommRingCat.of OpenRing) OpenRing :=
  ModuleCat.ofHom chartVolumeCoordinate.toLinearMap

private def coefficientIso : FourthModule ≅ ModuleCat.of (CommRingCat.of OpenRing) OpenRing where
  hom := coefficientHom
  inv := ModuleCat.ofHom chartVolumeCoordinate.symm.toLinearMap
  hom_inv_id := by
    apply ConcreteCategory.hom_ext
    intro x
    exact chartVolumeCoordinate.symm_apply_apply x
  inv_hom_id := by
    apply ConcreteCategory.hom_ext
    intro x
    exact chartVolumeCoordinate.apply_symm_apply x

/-- The fourth exterior power sheaf on the original Jacobian chart in the coordinate volume. -/
def volumeIso : fourForms ≅ structureModule :=
  (tilde.functor (CommRingCat.of OpenRing)).mapIso coefficientIso ≪≫ tildeSelf

def fourthSection (U : Jacobian.Opens) (w : Fourth) : additiveFourForms.obj.obj (op U) :=
  tilde.toOpen FourthModule U w

theorem volumeIso_toOpen (U : Jacobian.Opens) (w : Fourth) :
    volumeIso.hom.val.app (op U) (fourthSection U w) =
      algebraMap OpenRing (AffineSections (A := OpenRing) U) (chartVolumeCoordinate w) := by
  have h := ConcreteCategory.congr_hom (C := ModuleCat (CommRingCat.of OpenRing))
    (tilde.toOpen_map_app (R := CommRingCat.of OpenRing) coefficientHom U) w
  change _ = algebraMap OpenRing (AffineSections (A := OpenRing) U) (chartVolumeCoordinate w) at h
  exact h

theorem volumeIso_hom_inv (U : Jacobian.Opens) (x : additiveFunctions.obj.obj (op U)) :
    volumeIso.hom.val.app (op U) (volumeIso.inv.val.app (op U) x) = x :=
  congrArg (fun f : structureModule ⟶ structureModule => f.val.app (op U) x) volumeIso.inv_hom_id

def exteriorDifferential : additiveForms ⟶ additiveFourForms :=
  topDifferential ≫ (SheafOfModules.toSheaf Jacobian.ringCatSheaf).map volumeIso.inv

def protectedVolumeSection (U : Jacobian.Opens) : additiveFourForms.obj.obj (op U) :=
  fourthSection U (protectedCoefficient • chartVolume)

theorem protectedVolumeSection_restrict {U V : Jacobian.Opens} (h : V ≤ U) :
    additiveFourForms.obj.map (homOfLE h).op (protectedVolumeSection U) =
      protectedVolumeSection V := rfl

theorem protectedVolumeSection_coordinate (U : Jacobian.Opens) :
    volumeIso.hom.val.app (op U) (protectedVolumeSection U) = protectedSection U := by
  rw [protectedVolumeSection, volumeIso_toOpen, map_smul, chartVolumeCoordinate_chartVolume,
    smul_eq_mul, mul_one]
  rfl

/-- The scalar boundary equation tests equality of the actual exterior sections on each open. -/
theorem exteriorDifferential_eq_protected_iff (U : Jacobian.Opens) (w : additiveForms.obj.obj (op U)) :
    exteriorDifferential.hom.app (op U) w = protectedVolumeSection U ↔
      topDifferential.hom.app (op U) w = protectedSection U := by
  change volumeIso.inv.val.app (op U) (topDifferential.hom.app (op U) w) = _ ↔ _
  constructor
  · intro h
    simpa only [volumeIso_hom_inv, protectedVolumeSection_coordinate] using
      congrArg (volumeIso.hom.val.app (op U)) h
  · intro h
    rw [h, ← protectedVolumeSection_coordinate]
    exact congrArg (fun f : fourForms ⟶ fourForms => f.val.app (op U) (protectedVolumeSection U))
      volumeIso.hom_inv_id

/-- Evaluate a section of the fourth power in the Kähler exterior module of the localized ring. -/
def readLocalFourth (s : OpenRing) (w : additiveFourForms.obj.obj (op (PrimeSpectrum.basicOpen s))) :
    Form s 4 :=
  (basicSectionsEquiv s).symm (volumeIso.hom.val.app (op (PrimeSpectrum.basicOpen s)) w) • volume s

theorem readLocalFourth_volume (s : OpenRing) :
    readLocalFourth s (fourthSection (PrimeSpectrum.basicOpen s) chartVolume) = volume s := by
  simp only [readLocalFourth, volumeIso_toOpen, chartVolumeCoordinate_chartVolume, map_one]
  exact one_smul (LocalRing s) (volume s)

theorem readLocalFourth_protected (s : OpenRing) :
    readLocalFourth s (protectedVolumeSection (PrimeSpectrum.basicOpen s)) =
      residueSourceForm s affineA := by
  rw [readLocalFourth, protectedVolumeSection_coordinate, protectedSection_principal, residueSourceForm]

theorem readLocalFourth_exteriorDifferential (s : OpenRing) (hs : s ≠ 0)
    (w : additiveForms.obj.obj (op (PrimeSpectrum.basicOpen s))) :
    readLocalFourth s (exteriorDifferential.hom.app (op (PrimeSpectrum.basicOpen s)) w) =
      exteriorD3 s (readLocal s w) := by
  change (basicSectionsEquiv s).symm (volumeIso.hom.val.app _
    (volumeIso.inv.val.app _ (topDifferential.hom.app _ w))) • volume s = _
  rw [volumeIso_hom_inv, readLocal_differential s hs]

end CycleQ2LiteralResidueSheaf
end

#print axioms CycleQ2LiteralResidueSheaf.readLocalFourth_protected
#print axioms CycleQ2LiteralResidueSheaf.readLocalFourth_exteriorDifferential
