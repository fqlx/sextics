import Mathlib.AlgebraicGeometry.Morphisms.Proper
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.RingTheory.Spectrum.Prime.Noetherian
import Proposal.GeometricAffineChartSections

/-!
# Regular functions on a connected reduced proper complex scheme

Each global function generates a finite-dimensional subalgebra over the base
field. Its discrete spectrum is a continuous image of the connected spectrum
of the global section ring. Reducedness then makes the subalgebra a field.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ProperGlobalFunctions

open CategoryTheory AlgebraicGeometry
open CycleQ2GeometricAffineChartSections (schemeCoefficient)

private theorem integralElement_isScalar {K R : Type*} [Field K] [IsAlgClosed K]
    [CommRing R] [Algebra K R] [Nontrivial R] [IsReduced R] [Algebra.IsIntegral K R]
    [PreconnectedSpace (PrimeSpectrum R)] (x : R) : ∃ c : K, algebraMap K R c = x := by
  let A := Algebra.adjoin K ({x} : Set R)
  have : Module.Finite K A :=
    Algebra.finite_adjoin_simple_of_isIntegral (Algebra.IsIntegral.isIntegral x)
  have : IsArtinianRing A := IsArtinianRing.of_finite K A
  have : Algebra.IsIntegral A R := Algebra.IsIntegral.tower_top K
  have hs := Algebra.IsIntegral.comap_surjective A R
  have : PreconnectedSpace (PrimeSpectrum A) :=
    hs.denseRange.preconnectedSpace (PrimeSpectrum.continuous_comap _)
  have : _root_.IsReduced A := isReduced_of_injective A.val Subtype.val_injective
  have hfield := PrimeSpectrum.subsingleton_iff_isField_of_isReduced.mp
    (subsingleton_of_preconnected_totallyDisconnected : Subsingleton (PrimeSpectrum A))
  have : IsDomain A := hfield.isDomain
  let x' : A := ⟨x, Algebra.subset_adjoin (Set.mem_singleton x)⟩
  obtain ⟨c, hc⟩ := (IsAlgClosed.algebraMap_bijective_of_isIntegral (k := K) (K := A)).2 x'
  exact ⟨c, congrArg Subtype.val hc⟩

private theorem surjective_of_integral {K R : Type*} [Field K] [IsAlgClosed K]
    [CommRing R] [Nontrivial R] [IsReduced R] [PreconnectedSpace (PrimeSpectrum R)]
    (f : K →+* R) (hf : f.IsIntegral) : Function.Surjective f := by
  let _ : Algebra K R := f.toAlgebra
  have : Algebra.IsIntegral K R := ⟨hf⟩
  exact integralElement_isScalar (K := K) (R := R)

/-- The structural coefficient map exhausts global functions on a connected
reduced complex scheme universally closed over the point. -/
theorem schemeCoefficient_surjective {X : Scheme.{0}} [ConnectedSpace X]
    [AlgebraicGeometry.IsReduced X] (f : X ⟶ Spec (CommRingCat.of ℂ))
    [UniversallyClosed f] : Function.Surjective (schemeCoefficient f) := by
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : PreconnectedSpace (PrimeSpectrum Γ(X, ⊤)) :=
    X.toSpecΓ.denseRange.preconnectedSpace X.toSpecΓ.continuous
  have : Nonempty (⊤ : X.Opens) := ⟨⟨Classical.arbitrary X, trivial⟩⟩
  let F := schemeCoefficient f
  have hF : F.IsIntegral := by
    apply RingHom.isIntegral_respectsIso.2 (e := (Scheme.ΓSpecIso _).symm.commRingCatIsoToRingEquiv)
    exact isIntegral_appTop_of_universallyClosed f
  exact surjective_of_integral F hF

end CycleQ2ProperGlobalFunctions

#print axioms CycleQ2ProperGlobalFunctions.schemeCoefficient_surjective
