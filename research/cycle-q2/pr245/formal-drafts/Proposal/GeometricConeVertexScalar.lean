import Proposal.GeometricConeSimplexNumerator

/-! The coefficient of the simplex vertex after normalized normal contraction
is the explicit jet residue on the original derivative open. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2ConeVertexScalar

open MvPolynomial CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2ConeSimplexRings (Ambient Divisor quotient coord embed embed_injective embed_polynomial)
open CycleQ2WeightedConeVertex (GradientRing grad residueSection evalSection coneNumerator)
open CycleQ2WeightedCechPresentations (derivative_mem denominators)
open CycleQ2WeightedConePartial (RF value)
open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2ConeSimplexNumerator (vCoeff vCoeff_field)
open CycleQ2LogCofactorClosure (half)
open CycleQ2LogFractionComparison (ambientFrame ambient_partial)
open CycleQ2LogarithmicDifferential (coordDeriv)
open CycleQ2WeightedDoublePoleCech (vertex)

variable {k : Type} [Field k] [CharZero k]
local notation "P" => MvPolynomial (Fin 5) k
local notation "K" => RF (Fin 5) k

section Gradient
variable (G : P) (T : Finset (Fin 5)) (i : Fin 5) (hi : i ∈ T)
local notation "A" => Ambient G T
local notation "M" => denominators G (T : Set (Fin 5))

/-- The unit used by the normalized normal field in the simplex ring. -/
def gradientUnit : Aˣ :=
  (IsLocalization.map_units A (⟨pderiv i G, derivative_mem G (show i ∈ (T : Set _) from hi)⟩ : M)).unit

def invGrad : A := ↑(gradientUnit G T i hi)⁻¹

theorem grad_mul_invGrad :
    algebraMap P A (grad i G) * invGrad G T i hi = 1 := (gradientUnit G T i hi).mul_inv

theorem normal_coordinate :
    CycleQ2ConeSimplexRings.normal G hi (coord G T i) = invGrad G T i hi := by
  change invGrad G T i hi * CycleQ2PoleReductionGradient.partial M i
    (algebraMap P A (X i)) = _
  rw [CycleQ2PoleReductionGradient.partial_map, pderiv_X_self, map_one, mul_one]

/-- Restriction from the single gradient localization to the full simplex ring. -/
def sectionTo : GradientRing i G →+* A :=
  IsLocalization.Away.lift (grad i G)
    (show IsUnit (algebraMap P A (grad i G)) from
      IsLocalization.map_units A (⟨_, derivative_mem G (show i ∈ (T : Set _) from hi)⟩ : M))

@[simp] theorem sectionTo_polynomial (p : P) :
    sectionTo G T i hi (algebraMap P (GradientRing i G) p) = algebraMap P A p :=
  IsLocalization.Away.lift_eq _ _ _

theorem sectionTo_eval {E : Type*} [Field E] (e : A →+* E) (g : P →+* E)
    (he : ∀ p, e (algebraMap P A p) = g p) (hn : g (grad i G) ≠ 0) (c : GradientRing i G) :
    e (sectionTo G T i hi c) = evalSection i G g hn c := by
  have h : e.comp (sectionTo G T i hi) = evalSection i G g hn := by
    apply IsLocalization.ringHom_ext (Submonoid.powers (grad i G))
    ext1 p
    change e (sectionTo G T i hi (algebraMap P (GradientRing i G) p)) =
      evalSection i G g hn (algebraMap P (GradientRing i G) p)
    rw [sectionTo_polynomial, he]
    exact (IsLocalization.Away.lift_eq _ _ _).symm
  exact DFunLike.congr_fun h c

variable (hT : ∀ a ∈ T, pderiv a G ≠ 0)
private theorem grad_ne : value (grad i G) ≠ 0 :=
  fun h => hT i hi (IsFractionRing.to_map_eq_zero_iff.mp h)

theorem invGrad_field : embed G T hT (invGrad G T i hi) = (value (grad i G))⁻¹ := by
  apply mul_left_cancel₀ (grad_ne G T i hi hT)
  rw [mul_inv_cancel₀ (grad_ne G T i hi hT), ← embed_polynomial G T hT (grad i G),
    ← map_mul, grad_mul_invGrad, map_one]

end Gradient

variable (φ : CoeffRing →+* k) (T : Finset (Fin 5))
local notation "G" => equation φ
local notation "F" => value G
local notation "N" => value (coneNumerator k)
local notation "D" => coordDeriv (ambientFrame (I := Fin 5) (k := k))
variable (hT : ∀ a ∈ T, pderiv a G ≠ 0) (i : Fin 5) (hi : i ∈ T)

/-- The regular scalar multiplying the complementary wedge on any simplex
containing i is the restriction of the single-gradient jet residue. -/
theorem normalized_vertex :
    vCoeff φ T hT i hi * invGrad G T i hi =
      sectionTo G T i hi (residueSection i G (coneNumerator k)) := by
  apply embed_injective G T hT
  rw [map_mul, vCoeff_field, invGrad_field,
    sectionTo_eval G T i hi (embed G T hT).toRingHom value (embed_polynomial G T hT)
      (grad_ne G T i hi hT)]
  have hd : D = CycleQ2WeightedConeCech.D (L := k) := funext ambient_partial
  calc
    _ = F * vertex D F N i / (2 * value (grad i G)) := by
      have hh : half (k := k) = (2 : K)⁻¹ := by simp [half]
      rw [hh, div_eq_mul_inv, mul_inv_rev]
      ring
    _ = _ := by
      simpa only [hd, CycleQ2WeightedDoublePoleCech.normal, CycleQ2WeightedConeCech.D,
        CycleQ2WeightedConeCech.F, CycleQ2WeightedConeCech.B, CycleQ2WeightedConePartial.partial_map,
        grad] using CycleQ2WeightedConeCech.cone_vertex_residue φ i (hT i hi)

/-- The same identity in the native quotient chart of the actual cone divisor. -/
theorem divisor_vertex :
    quotient G T (vCoeff φ T hT i hi * invGrad G T i hi) =
      quotient G T (sectionTo G T i hi (residueSection i G (coneNumerator k))) :=
  congrArg (quotient G T) (normalized_vertex φ T hT i hi)

end CycleQ2ConeVertexScalar
end

#print axioms CycleQ2ConeVertexScalar.normal_coordinate
#print axioms CycleQ2ConeVertexScalar.normalized_vertex
