import Proposal.GeometricGradientSimplex
import Proposal.GeometricLocalizationFractionEmbedding

/-!
# Common meromorphic field of derivative simplices

The regular ambient rings and their hypersurface quotients are those of
the derivative opens. Their embeddings in the ambient rational function
field commute with every simplex restriction.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2ConeSimplexRings

open MvPolynomial
open CycleQ2WeightedCechPresentations (denominators)

variable {k : Type} [CommRing k]
abbrev P (k : Type) [CommRing k] := MvPolynomial (Fin 5) k
variable (G : P k)

abbrev Ambient (T : Finset (Fin 5)) := CycleQ2GradientSimplex.Ambient G (T : Set (Fin 5))
abbrev Divisor (T : Finset (Fin 5)) := CycleQ2GradientSimplex.Divisor G (T : Set (Fin 5))
abbrev eqn (T : Finset (Fin 5)) := CycleQ2GradientSimplex.f G (T : Set (Fin 5))
abbrev quotient (T : Finset (Fin 5)) := CycleQ2GradientSimplex.π G (T : Set (Fin 5))
abbrev coord (T : Finset (Fin 5)) := CycleQ2GradientSimplex.coord G (T : Set (Fin 5))
abbrev ambientBasis (T : Finset (Fin 5)) := CycleQ2GradientSimplex.ambientBasis G (T : Set (Fin 5))

variable {T U : Finset (Fin 5)}
abbrev restrictAmbient (h : T ⊆ U) : Ambient G T →ₐ[k] Ambient G U :=
  CycleQ2GradientSimplex.ambientMap G (s := (T : Set (Fin 5))) (t := (U : Set (Fin 5))) h
abbrev restrictDivisor (h : T ⊆ U) : Divisor G T →ₐ[k] Divisor G U :=
  CycleQ2GradientSimplex.divisorMap G (s := (T : Set (Fin 5))) (t := (U : Set (Fin 5))) h

theorem restriction_square (h : T ⊆ U) :
    (quotient G U).comp (restrictAmbient G h) = (restrictDivisor G h).comp (quotient G T) :=
  CycleQ2GradientSimplex.restrict_square G h

abbrev normal {i : Fin 5} (hi : i ∈ T) :=
  CycleQ2GradientSimplex.normal G (T : Set (Fin 5)) i hi

@[simp] theorem normal_eqn {i : Fin 5} (hi : i ∈ T) : normal G hi (eqn G T) = 1 :=
  CycleQ2GradientSimplex.normal_f G _ i hi

@[simp] theorem quotient_eqn (T : Finset (Fin 5)) : quotient G T (eqn G T) = 0 :=
  CycleQ2GradientSimplex.π_f G _

/-- An identically zero member of the derivative simplex cuts out the empty ambient open. -/
theorem ambient_empty {i : Fin 5} (hi : i ∈ T) (hz : pderiv i G = 0) :
    Subsingleton (Ambient G T) := by
  have h := IsLocalization.map_units (Ambient G T)
    (⟨pderiv i G, CycleQ2WeightedCechPresentations.derivative_mem G
      (show i ∈ (T : Set (Fin 5)) from hi)⟩ : denominators G (T : Set (Fin 5)))
  change IsUnit (algebraMap (P k) (Ambient G T) (pderiv i G)) at h
  rw [hz, map_zero] at h
  exact subsingleton_of_zero_eq_one (isUnit_zero_iff.mp h)

theorem divisor_empty {i : Fin 5} (hi : i ∈ T) (hz : pderiv i G = 0) :
    Subsingleton (Divisor G T) := by
  haveI := ambient_empty G hi hz
  apply subsingleton_of_zero_eq_one
  simpa only [map_zero, map_one] using congrArg (quotient G T)
    (Subsingleton.elim (0 : Ambient G T) 1)

section Field
variable [IsDomain k]

theorem regular_denominators (T : Finset (Fin 5)) (hT : ∀ i ∈ T, pderiv i G ≠ 0) :
    denominators G (T : Set (Fin 5)) ≤ nonZeroDivisors (P k) := by
  apply Submonoid.closure_le.mpr
  rintro _ ⟨i,hi,rfl⟩
  exact mem_nonZeroDivisors_iff_ne_zero.mpr (hT i hi)

abbrev K (k : Type) [CommRing k] [IsDomain k] := FractionRing (P k)

def embed (T : Finset (Fin 5)) (hT : ∀ i ∈ T, pderiv i G ≠ 0) :
    Ambient G T →ₐ[k] K k :=
  CycleQ2LocalizationFractionEmbedding.map _ (regular_denominators G T hT)

@[simp] theorem embed_polynomial (T : Finset (Fin 5)) (hT : ∀ i ∈ T, pderiv i G ≠ 0) (p : P k) :
    embed G T hT (algebraMap (P k) (Ambient G T) p) = algebraMap (P k) (K k) p :=
  CycleQ2LocalizationFractionEmbedding.map_polynomial _ _ _

theorem embed_injective (T : Finset (Fin 5)) (hT : ∀ i ∈ T, pderiv i G ≠ 0) :
    Function.Injective (embed G T hT) :=
  CycleQ2LocalizationFractionEmbedding.injective (k := k) _ (regular_denominators G T hT)

theorem embed_restrict (h : T ⊆ U) (hU : ∀ i ∈ U, pderiv i G ≠ 0) :
    (embed G U hU).comp (restrictAmbient G h) = embed G T (fun i hi => hU i (h hi)) := by
  apply IsLocalization.algHom_ext (denominators G (T : Set (Fin 5)))
  ext1 p
  change embed G U hU (restrictAmbient G h (algebraMap (P k) (Ambient G T) p)) =
    embed G T _ (algebraMap (P k) (Ambient G T) p)
  rw [CycleQ2GradientSimplex.ambientMap_polynomial, embed_polynomial, embed_polynomial]

abbrev fracAlgebra (T : Finset (Fin 5)) (hT : ∀ i ∈ T, pderiv i G ≠ 0) :
    Algebra (Ambient G T) (K k) := (embed G T hT).toRingHom.toAlgebra

theorem fracTower (T : Finset (Fin 5)) (hT : ∀ i ∈ T, pderiv i G ≠ 0) :
    letI := fracAlgebra G T hT
    IsScalarTower k (Ambient G T) (K k) := IsScalarTower.of_algHom (embed G T hT)

theorem fracLocalization (T : Finset (Fin 5)) (hT : ∀ i ∈ T, pderiv i G ≠ 0) :
    letI := fracAlgebra G T hT
    IsFractionRing (Ambient G T) (K k) :=
  CycleQ2LocalizationFractionEmbedding.fieldLocalization (k := k) _ (regular_denominators G T hT)

/-- The equation on a nonempty gradient chart defines a unit in the ambient rational field. -/
def fieldUnit (hG : G ≠ 0) : (K k)ˣ :=
  Units.mk0 (algebraMap (P k) (K k) G) (fun h =>
    hG ((IsFractionRing.injective (P k) (K k)) (h.trans (map_zero _).symm)))

@[simp] theorem embed_eqn (T : Finset (Fin 5)) (hT : ∀ i ∈ T, pderiv i G ≠ 0) (hG : G ≠ 0) :
    embed G T hT (eqn G T) = fieldUnit G hG := embed_polynomial G T hT G

theorem equation_ne_of_derivative {i : Fin 5} (hi : pderiv i G ≠ 0) : G ≠ 0 := by
  rintro rfl
  exact hi (map_zero _)

end Field
end CycleQ2ConeSimplexRings
end

#print axioms CycleQ2ConeSimplexRings.embed_restrict
#print axioms CycleQ2ConeSimplexRings.fracLocalization
