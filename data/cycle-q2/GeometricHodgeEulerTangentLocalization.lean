import Proposal.GeometricHodgeEuler
import Proposal.SolutionSupport07Part01
import Mathlib.Algebra.Module.FinitePresentation
import Mathlib.RingTheory.Extension.Cotangent.Basic
import Mathlib.RingTheory.Kaehler.TensorProduct

/-!
# Localization of the tangent module of the original affine charts

Kähler differentials commute with localization. The finite presentation
of the cotangent module makes the dual comparison a module localization.
The resulting map on derivations is the actual extension from the
Leibniz rule, and is identified on the entire localized algebra.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/
set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeEulerTangentLocalization

variable {K A B : Type*} [CommRing K] [CommRing A] [CommRing B]
  [Algebra K A] [Algebra A B] [Algebra K B] [IsScalarTower K A B]
  (S : Submonoid A) [IsLocalization S B]

def localizeDual : (Ω[A⁄K] →ₗ[A] A) →ₗ[A] (Ω[B⁄K] →ₗ[B] B) :=
  IsLocalizedModule.mapExtendScalars S (KaehlerDifferential.map K K A B) (Algebra.linearMap A B) B

def localize : Derivation K A A →ₗ[A] Derivation K B B :=
  ((KaehlerDifferential.linearMapEquivDerivation K B).restrictScalars A).toLinearMap ∘ₗ
    (localizeDual S ∘ₗ (KaehlerDifferential.linearMapEquivDerivation K A).symm.toLinearMap)

theorem localize_apply (D : Derivation K A A) (a : A) :
    localize (B := B) S D (algebraMap A B a) = algebraMap A B (D a) := by
  change localizeDual S D.liftKaehlerDifferential
    (KaehlerDifferential.D K B (algebraMap A B a)) = _
  rw [← KaehlerDifferential.map_D K K A B]
  exact (IsLocalizedModule.map_apply S (KaehlerDifferential.map K K A B)
    (Algebra.linearMap A B) D.liftKaehlerDifferential (KaehlerDifferential.D K A a)).trans
    (congrArg (algebraMap A B) (D.liftKaehlerDifferential_comp_D a))

theorem localize_eq_extend (D : Derivation K A A) :
    localize (B := B) S D = CycleQ2LocalizationDerivation.extend (S := B) S D :=
  CycleQ2LocalizationDerivation.extend_unique S D _ (localize_apply S D)

instance localize_isLocalized [Module.FinitePresentation A Ω[A⁄K]] :
    IsLocalizedModule S (localize (K := K) (B := B) S) := by
  let : IsLocalizedModule S (localizeDual (K := K) (B := B) S) := by
    unfold localizeDual
    infer_instance
  unfold localize
  infer_instance

open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2HodgeEuler

/-- Every complex weighted sextic chart has finitely presented differentials. -/
instance chartCotangentFinite (φ : CoeffRing →+* ℂ) (i : Fin 4) :
    Module.FinitePresentation (chart φ i) Ω[chart φ i⁄ℂ] := by
  exact Module.finitePresentation_of_finite _ _

theorem chart_localize (φ : CoeffRing →+* ℂ) (i : Fin 4) (z : chart φ i) :
    IsLocalizedModule (Submonoid.powers z)
      (localize (K := ℂ) (B := Localization.Away z) (Submonoid.powers z)) := inferInstance

end CycleQ2HodgeEulerTangentLocalization
end

#print axioms CycleQ2HodgeEulerTangentLocalization.localize_eq_extend
#print axioms CycleQ2HodgeEulerTangentLocalization.chart_localize
