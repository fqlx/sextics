import Proposal.GeometricGenericPointAffineSections
import Proposal.GeometricNormalCurveSmooth
import Mathlib.RingTheory.NoetherNormalization
import Mathlib.RingTheory.DedekindDomain.IntegralClosure
import Mathlib.RingTheory.Polynomial.UniqueFactorization
import Mathlib.RingTheory.Localization.Finiteness
import Mathlib.RingTheory.Algebraic.Integral
import Mathlib.AlgebraicGeometry.Morphisms.Proper

/-!
# Absolute normalization of an integral proper curve

Normalizing in the scheme's own generic residue field gives a finite map.
In dimension at most one its source is smooth over the characteristic-zero
base field, and it is proper whenever the original curve is proper.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2IntegralCurveNormalization

open CategoryTheory AlgebraicGeometry TopologicalSpace CycleQ2GenericPointAffineSections
open scoped nonZeroDivisors

/-- Noether normalization and separability give a finite integral closure inside
any chosen fraction field of a finite-type domain over a characteristic-zero field. -/
theorem finite_fraction_integralClosure (k A L : Type*) [Field k] [CharZero k] [CommRing A]
    [IsDomain A] [Algebra k A] [Algebra.FiniteType k A] [Field L] [Algebra A L]
    [IsFractionRing A L] : Module.Finite A (integralClosure A L) := by
  obtain ⟨n, g, hinj, hfin⟩ := exists_finite_inj_algHom_of_fg k A
  let P := MvPolynomial (Fin n) k
  let N := integralClosure A L
  let : Algebra P A := g.toRingHom.toAlgebra
  let : Module.Finite P A := hfin
  let : FaithfulSMul P A := (faithfulSMul_iff_algebraMap_injective P A).mpr hinj
  let : Algebra P L := ((algebraMap A L).comp g.toRingHom).toAlgebra
  let : IsScalarTower P A L := .of_algebraMap_eq' rfl
  let : FaithfulSMul P L := (faithfulSMul_iff_algebraMap_injective P L).mpr
    ((IsFractionRing.injective A L).comp hinj)
  let : Algebra (FractionRing P) L := FractionRing.liftAlgebra P L
  let : FiniteDimensional (FractionRing P) L := Module.Finite.of_isLocalization P A P⁰
  let : Algebra P N := ((algebraMap A N).comp g.toRingHom).toAlgebra
  let : IsScalarTower P A N := .of_algebraMap_eq' rfl
  let : IsScalarTower P N L := .of_algebraMap_eq' rfl
  let : IsIntegralClosure N P L := {
    algebraMap_injective := Subtype.val_injective
    isIntegral_iff := by
      intro x
      exact ⟨fun h => ⟨⟨x, h.tower_top⟩, rfl⟩,
        fun ⟨y, hy⟩ => hy ▸ isIntegral_trans (R := P) (y : L) y.property⟩ }
  let : Module.Finite P N := IsIntegralClosure.finite P (FractionRing P) L N
  exact Module.Finite.of_restrictScalars_finite P A N

universe u

variable (k : Type u) [Field k] [CharZero k] {X : Scheme.{u}} [IsIntegral X]

abbrev Model (X : Scheme.{u}) [IsIntegral X] := (point X).normalization

abbrev normalize (X : Scheme.{u}) [IsIntegral X] : Model X ⟶ X := (point X).fromNormalization

variable (p : X ⟶ Spec (CommRingCat.of k)) [LocallyOfFiniteType p]

def coefficientMap (U : X.Opens) : CommRingCat.of k ⟶ Γ(X,U) :=
  (Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ p.appLE ⊤ U (by simp)

omit [CharZero k] [IsIntegral X] in
theorem finiteType_coefficients {U : X.Opens} (hU : IsAffineOpen U) :
    (coefficientMap k p U).hom.FiniteType :=
  (p.finiteType_appLE (isAffineOpen_top _) hU (by simp)).comp
    (RingHom.FiniteType.of_surjective _ (Scheme.ΓSpecIso (CommRingCat.of k)).symm.commRingCatIsoToRingEquiv.surjective)

omit [CharZero k] [IsIntegral X] [LocallyOfFiniteType p] in
theorem fromSpec_over {U : X.Opens} (hU : IsAffineOpen U) :
    hU.fromSpec ≫ p = Spec.map (coefficientMap k p U) := by
  rw [coefficientMap, Spec.map_comp]
  have h := IsAffineOpen.SpecMap_appLE_fromSpec p (isAffineOpen_top _) hU (by simp)
  rw [IsAffineOpen.fromSpec_top, Scheme.isoSpec_Spec_inv] at h
  exact h.symm

omit [IsIntegral X] in
theorem nonempty_chart {U : X.Opens} (hU : IsAffineOpen U)
    [Nontrivial Γ(X,U)] : Nonempty U :=
  Nonempty.map hU.isoSpec.inv (inferInstance : Nonempty (Spec Γ(X,U)))

include p in
theorem finite_chart {U : X.Opens} (hU : IsAffineOpen U) :
    let := ((point X).app U).hom.toAlgebra
    Module.Finite Γ(X,U) (integralClosure Γ(X,U) Γ(pointScheme X, point X ⁻¹ᵁ U)) := by
  let A := Γ(X,U)
  let L := Γ(pointScheme X, point X ⁻¹ᵁ U)
  let : Algebra A L := ((point X).app U).hom.toAlgebra
  rcases subsingleton_or_nontrivial A with h | h
  · let : Subsingleton (integralClosure A L) := Algebra.subsingleton A _
    infer_instance
  let : Nonempty U := nonempty_chart hU
  let : Field L := (native_isField X U).toField
  let : IsFractionRing A L := native_isFractionRing X U hU
  let : Algebra k A := (coefficientMap k p U).hom.toAlgebra
  let : Algebra.FiniteType k A := finiteType_coefficients k p hU
  exact finite_fraction_integralClosure k A L

include p in
theorem finite : IsFinite (normalize X) := by
  refine { toIsAffineHom := inferInstance, finite_app := ?_ }
  intro U hU
  rw [Scheme.Hom.fromNormalization_app _ hU, CommRingCat.hom_comp]
  let := ((point X).app U).hom.toAlgebra
  exact (RingHom.Finite.of_surjective _ ((point X).normalizationObjIso hU).symm.commRingCatIsoToRingEquiv.surjective).comp
    (RingHom.finite_algebraMap.mpr (finite_chart k p hU))

omit [LocallyOfFiniteType p] in
theorem proper [IsProper p] : IsProper (normalize X ≫ p) := by
  have := finite k p
  infer_instance

theorem smooth_of_affine_dimension (hdim : ∀ U : X.affineOpens, Ring.KrullDimLE 1 Γ(X, U.1)) :
    Smooth (normalize X ≫ p) := by
  let j := point X
  apply (IsZariskiLocalAtSource.iff_of_openCover j.normalizationOpenCover).mpr
  intro U
  rw [← Category.assoc, Scheme.Hom.ι_fromNormalization, Category.assoc, fromSpec_over k p U.2,
    ← Spec.map_comp]
  apply (HasRingHomProperty.Spec_iff (P := @Smooth)).mpr
  let A := Γ(X,U.1)
  let L := Γ(pointScheme X, j ⁻¹ᵁ U.1)
  let : Algebra A L := (j.app U.1).hom.toAlgebra
  let N := integralClosure A L
  let : Algebra k A := (coefficientMap k p U.1).hom.toAlgebra
  let : Algebra k N := ((algebraMap A N).comp (algebraMap k A)).toAlgebra
  change (algebraMap k N).Smooth
  apply RingHom.smooth_algebraMap.mpr
  rcases subsingleton_or_nontrivial A with h | h
  · let : Subsingleton N := Algebra.subsingleton A _
    infer_instance
  let : Nonempty U.1 := nonempty_chart U.2
  let : Field L := (native_isField X U.1).toField
  let : Algebra.FiniteType k A := finiteType_coefficients k p U.2
  let : Ring.KrullDimLE 1 A := hdim U
  let : Module.Finite A N := finite_chart k p U.2
  exact CycleQ2NormalCurveSmooth.smooth_finite_integralClosure k A L

theorem smooth (hdim : topologicalKrullDim X ≤ 1) : Smooth (normalize X ≫ p) := by
  apply smooth_of_affine_dimension k p
  intro U
  apply Ring.krullDimLE_iff.mpr
  rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (U.2.fromSpec.isOpenEmbedding.isInducing.topologicalKrullDim_le).trans hdim

end CycleQ2IntegralCurveNormalization
end

#print axioms CycleQ2IntegralCurveNormalization.finite
#print axioms CycleQ2IntegralCurveNormalization.proper
#print axioms CycleQ2IntegralCurveNormalization.smooth_of_affine_dimension
#print axioms CycleQ2IntegralCurveNormalization.smooth
