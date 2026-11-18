import Proposal.GeometricOmittedCoordinateBasis
import Proposal.GeometricPoleReductionRadial

/-! Coordinate differential frames on every intersection of cone gradient opens. -/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2ConeGradientBasis
open MvPolynomial CycleQ2PoleReductionGradient CycleQ2PoleReductionRadial
variable {k : Type} [CommRing k] (S : Submonoid (Poly k)) (F : Poly k)
  (i : Fin 5) (hi : pderiv i F ∈ S)
local notation "B" => Localization S
local notation "ι" => algebraMap (Poly k) B
local notation "G" => ι F
local notation "Q" => Divisor G
local notation "q" => Ideal.Quotient.mk (divisorIdeal G)
local notation "dB" => KaehlerDifferential.D k B
local notation "dQ" => KaehlerDifferential.D k Q

private def adjusted (j : Fin 4) : Derivation k B B :=
  partial S (i.succAbove j) - partial S (i.succAbove j) G • normal S F i hi

private theorem adjusted_F (j : Fin 4) : adjusted S F i hi j G = 0 * G := by
  rw [adjusted, Derivation.sub_apply, Derivation.smul_apply, normal_equation, smul_eq_mul,
    mul_one, sub_self, zero_mul]

/-- Coordinate derivatives at fixed equation on the localized cone divisor. -/
def tangent (j : Fin 4) : Derivation k Q Q :=
  onDivisor G 0 (adjusted S F i hi j) (adjusted_F S F i hi j)

private theorem normal_other (a : Fin 4) : normal S F i hi (ι (X (i.succAbove a))) = 0 := by
  simp only [normal, Derivation.smul_apply, partial_map, pderiv_X_of_ne (i.succAbove_ne a),
    map_zero, smul_zero]

theorem tangent_coord (j a : Fin 4) :
    tangent S F i hi j (q (ι (X (i.succAbove a)))) = if a = j then 1 else 0 := by
  unfold tangent
  rw [onDivisor_mk, adjusted, Derivation.sub_apply, Derivation.smul_apply, normal_other,
    smul_zero, sub_zero, partial_map]
  by_cases h : a = j
  · subst a
    simp only [pderiv_X_self, map_one, if_pos rfl]
  · have ha : i.succAbove a ≠ i.succAbove j := fun e => h (i.succAbove_right_injective e)
    rw [pderiv_X_of_ne ha, map_zero, map_zero, if_neg h]

private def reduction := KaehlerDifferential.map k k B Q

private theorem reduction_surjective : Function.Surjective (reduction S F) :=
  KaehlerDifferential.map_surjective_of_surjective k k B Q Ideal.Quotient.mk_surjective

private theorem reduction_F : reduction S F (dB G) = 0 := by
  rw [reduction, KaehlerDifferential.map_D]
  have hq : q G = 0 := Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))
  change dQ (q G) = 0
  rw [hq, map_zero]

private def partialUnit : Bˣ :=
  (IsLocalization.map_units B (⟨pderiv i F,hi⟩ : S)).unit

private theorem normal_coefficient : (coordinates S).repr (dB G) i = (partialUnit S F i hi : B) := by
  change (coordinates S).coord i (dB G) = _
  rw [← partial_covector, Derivation.liftKaehlerDifferential_comp_D, partial_map]
  exact (IsUnit.unit_spec (IsLocalization.map_units B (⟨pderiv i F,hi⟩ : S))).symm

private theorem reduction_coord (j : Fin 5) :
    reduction S F ((coordinates S) j) = dQ (q (ι (X j))) := by
  rw [coordinates_apply, reduction, KaehlerDifferential.map_D]

/-- On every localization containing ∂ᵢF, the four retained coordinate
differentials form a basis of the true Kähler module of the divisor. -/
def basis : Module.Basis (Fin 4) Q (KaehlerDifferential k Q) :=
  CycleQ2OmittedCoordinateBasis.basis (coordinates S) (reduction S F)
    (reduction_surjective S F) (dB G) (reduction_F S F) i (partialUnit S F i hi)
    (normal_coefficient S F i hi) (fun j => (tangent S F i hi j).liftKaehlerDifferential)
    (by intro j a; rw [reduction_coord, Derivation.liftKaehlerDifferential_comp_D, tangent_coord])

@[simp] theorem basis_apply (j : Fin 4) :
    basis S F i hi j = dQ (q (ι (X (i.succAbove j)))) := by
  rw [basis, CycleQ2OmittedCoordinateBasis.basis_apply, reduction_coord]

/-- The dual of the retained coordinate frame is the explicit tangent
derivation that holds the defining equation fixed. -/
theorem tangent_covector (j : Fin 4) :
    (tangent S F i hi j).liftKaehlerDifferential = (basis S F i hi).coord j := by
  apply (basis S F i hi).ext
  intro a
  rw [Module.Basis.coord_apply, Module.Basis.repr_self_apply, basis_apply,
    Derivation.liftKaehlerDifferential_comp_D, tangent_coord]

end CycleQ2ConeGradientBasis
end
#print axioms CycleQ2ConeGradientBasis.basis_apply
