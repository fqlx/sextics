import Proposal.GeometricConeSimplexClosure
import Proposal.GeometricConeSimplexRadialField
import Proposal.GeometricPoleReductionRadialResidue
import Proposal.GeometricPoleReductionRestriction

/-! The horizontal degree-three Čech cocycle of the weighted sextic as actual
forms on each divisor simplex. The same minus sign multiplies Euler insertion
of each noncontracted residue after incorporating the Čech residue sign. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2ConeSimplexRadialClosure

open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (equation)
open CycleQ2WeightedCechPresentations (denominators derivative_mem)
open CycleQ2LogarithmicDifferential (exteriorD)
open CycleQ2LogarithmicPullback (Forms)
open CycleQ2LogarithmicChartDerivative (pull)
open CycleQ2LiteralThreefoldResidueContraction (interior)
open CycleQ2ConeSimplexRings (Ambient Divisor quotient normal)
open CycleQ2ConeSimplexClosure (chart rv re rf)
open CycleQ2PoleReductionRadial (weightedDivisorEuler weighted_residue_interior)
open CycleQ2ConeSimplexRadialField (vr er fr vr_field er_field fr_field)
open CycleQ2LogarithmicResidue (localResidue_zero localResidue_sub localResidue_neg localResidue_add)
open MvPolynomial (pderiv)

variable {k : Type} [Field k] [CharZero k] (φ : CoeffRing →+* k)
local notation "G" => equation φ
variable (T : Finset (Fin 5)) (hT : ∀ i ∈ T, pderiv i G ≠ 0) (r : Fin 5) (hr : r ∈ T)
local notation "M" => denominators G (T : Set (Fin 5))
local notation "C" => chart φ T hT r hr

/-- Signed contraction on the cone quotient that descends to the projective cone slice. -/
def radialize (n : ℕ) : Forms k (Divisor G T) (n+1) →+ Forms k (Divisor G T) n :=
  -(interior n (weightedDivisorEuler M φ).liftKaehlerDifferential).toAddMonoidHom

abbrev zv (i : Fin 5) (hi : i ∈ T) := radialize φ T 3 (rv φ T hT r hr i hi)
abbrev ze (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) :=
  radialize φ T 2 (re φ T hT r hr i j hi hj)
abbrev zf (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) :=
  radialize φ T 1 (rf φ T hT r hr i j l hi hj hl)

local notation "V" => zv φ T hT r hr
local notation "E" => ze φ T hT r hr
local notation "A" => zf φ T hT r hr

theorem res_interior (n : ℕ) (m : Forms k (Ambient G T) (n+3)) (h : C.Logarithmic (n+3) m) :
    C.res (n+1) (interior (n+2) (CycleQ2PoleReductionRadial.radial M).liftKaehlerDifferential m) =
      radialize φ T (n+1) (C.res (n+2) m) := by
  obtain ⟨w, hw⟩ := h
  exact weighted_residue_interior M φ r (derivative_mem G hr) n m w hw

theorem vr_res (i : Fin 5) (hi : i ∈ T) :
    C.res 3 (vr φ T hT i hi) = V i hi :=
  res_interior φ T hT r hr 2 _ (CycleQ2ConeSimplexClosure.vertex_on φ T hT r hr i hi).1

theorem er_res (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) :
    C.res 2 (er φ T hT i j hi hj) = -E i j hi hj := by
  change C.res 2 (-interior 3 _ _) = _
  rw [show ∀ a, C.res 2 (-a) = -C.res 2 a from localResidue_neg _ _ _]
  exact congrArg Neg.neg (res_interior φ T hT r hr 1 _
    (CycleQ2ConeSimplexClosure.edge_on φ T hT r hr i j hi hj).1)

theorem fr_res (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) :
    C.res 1 (fr φ T hT i j l hi hj hl) = A i j l hi hj hl :=
  res_interior φ T hT r hr 0 _ (CycleQ2ConeSimplexClosure.face_on φ T hT r hr i j l hi hj hl).1

/-- Exterior differentiation of the signed three-form vertex. -/
theorem vertex_on (i : Fin 5) (hi : i ∈ T) :
    C.Logarithmic 4 (vr φ T hT i hi) ∧ exteriorD C.divisor 3 (V i hi) = 0 := by
  have h := C.realizes_d (CycleQ2LogCofactorClosure.equation_ne φ i (hT i hi))
    2 (vr φ T hT i hi) 0 (CycleQ2LogNormalizedEulerCech.v φ i) 0 (vr_field φ T hT i hi)
    (by simp [CycleQ2ConeLogClosure.Chart.Realizes])
    (CycleQ2LogNormalizedEulerCech.closed φ i i i i (hT i hi) (hT i hi) (hT i hi)).1
  rw [vr_res, show C.res 4 0 = 0 from localResidue_zero _ _ _, neg_zero] at h
  exact h

/-- The edge differential is the vertex at the last index minus the first. -/
theorem edge_on (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) :
    C.Logarithmic 3 (er φ T hT i j hi hj) ∧
    exteriorD C.divisor 2 (E i j hi hj) = V j hj - V i hi := by
  have h := C.realizes_d (CycleQ2LogCofactorClosure.equation_ne φ i (hT i hi))
    1 (er φ T hT i j hi hj) (vr φ T hT j hj - vr φ T hT i hi)
    (CycleQ2LogNormalizedEulerCech.e φ i j)
    (CycleQ2LogNormalizedEulerCech.v φ j-CycleQ2LogNormalizedEulerCech.v φ i)
    (er_field φ T hT i j hi hj)
    (by change pull C.embed 4 (_-_) = _; rw [map_sub,vr_field,vr_field,smul_sub])
    (CycleQ2LogNormalizedEulerCech.closed φ i j j j (hT i hi) (hT j hj) (hT j hj)).2.1
  have hd := h.2
  rw [er_res, map_neg, show ∀ a b, C.res 3 (a-b) = C.res 3 a-C.res 3 b from localResidue_sub _ _ _,
    vr_res, vr_res] at hd
  exact ⟨h.1,neg_injective hd⟩

/-- The face differential is the negative alternating edge boundary. -/
theorem face_on (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) :
    C.Logarithmic 2 (fr φ T hT i j l hi hj hl) ∧
    exteriorD C.divisor 1 (A i j l hi hj hl) = -(E j l hj hl-E i l hi hl+E i j hi hj) := by
  have h := C.realizes_d (CycleQ2LogCofactorClosure.equation_ne φ i (hT i hi))
    0 (fr φ T hT i j l hi hj hl) (-(er φ T hT j l hj hl-er φ T hT i l hi hl+er φ T hT i j hi hj))
    (CycleQ2LogNormalizedEulerCech.f φ i j l)
    (-(CycleQ2LogNormalizedEulerCech.e φ j l-CycleQ2LogNormalizedEulerCech.e φ i l+
      CycleQ2LogNormalizedEulerCech.e φ i j)) (fr_field φ T hT i j l hi hj hl)
    (by change pull C.embed 3 (-(_-_+_)) = _
        rw [map_neg,map_add,map_sub,er_field,er_field,er_field,smul_neg,smul_add,smul_sub])
    (CycleQ2LogNormalizedEulerCech.closed φ i j l l (hT i hi) (hT j hj) (hT l hl)).2.2.1
  have hd := h.2
  rw [fr_res,
    show ∀ a, C.res 2 (-a) = -C.res 2 a from localResidue_neg _ _ _,
    show ∀ a b, C.res 2 (a+b) = C.res 2 a+C.res 2 b from localResidue_add _ _ _,
    show ∀ a b, C.res 2 (a-b) = C.res 2 a-C.res 2 b from localResidue_sub _ _ _,
    er_res, er_res, er_res] at hd
  exact ⟨h.1, by rw [hd]; abel⟩

theorem tetrahedron_on (i j l m : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) (hm : m ∈ T) :
    A j l m hj hl hm-A i l m hi hl hm+A i j m hi hj hm-A i j l hi hj hl = 0 := by
  have h := CycleQ2ConeSimplexClosure.tetrahedron_on φ T hT r hr i j l m hi hj hl hm
  simpa only [zf, map_add,map_sub,map_zero] using congrArg (radialize φ T 1) h

section Restriction
variable {T} {U : Finset (Fin 5)}
open CycleQ2ConeSimplexRings (restrictAmbient restrictDivisor)
open CycleQ2PoleReductionRadial (radial radial_map)

theorem ambient_radial_restrict (h : T ⊆ U) (a : Ambient G T) :
    radial (denominators G (U : Set (Fin 5))) (restrictAmbient G h a) =
      restrictAmbient G h (radial (denominators G (T : Set (Fin 5))) a) := by
  apply CycleQ2PoleReductionRestriction.derivation_restrict (denominators G (T : Set (Fin 5)))
    (restrictAmbient G h).toRingHom
  intro p
  change radial _ (CycleQ2GradientSimplex.ambientMap G h (algebraMap _ _ p)) =
    CycleQ2GradientSimplex.ambientMap G h (radial _ (algebraMap _ _ p))
  rw [CycleQ2GradientSimplex.ambientMap_polynomial,radial_map,radial_map,
    CycleQ2GradientSimplex.ambientMap_polynomial]

private theorem euler_quotient (U : Finset (Fin 5)) (a : Ambient G U) :
    weightedDivisorEuler (denominators G (U : Set (Fin 5))) φ (quotient G U a) =
      quotient G U (radial (denominators G (U : Set (Fin 5))) a) :=
  CycleQ2PoleReductionRadial.onDivisor_mk _ _ _ _ _

theorem divisor_radial_restrict (h : T ⊆ U) (a : Divisor G T) :
    weightedDivisorEuler (denominators G (U : Set (Fin 5))) φ (restrictDivisor G h a) =
      restrictDivisor G h (weightedDivisorEuler (denominators G (T : Set (Fin 5))) φ a) := by
  obtain ⟨x,rfl⟩ := Ideal.Quotient.mk_surjective a
  change weightedDivisorEuler _ φ (quotient G U (restrictAmbient G h x)) =
    restrictDivisor G h (weightedDivisorEuler _ φ (quotient G T x))
  rw [euler_quotient,euler_quotient]
  exact congrArg (quotient G U) (ambient_radial_restrict φ h x)

/-- Restrictions of the three signed radialized rows are computed directly
by the native divisor restriction, for any lower-dimensional face. -/
theorem radialize_restrict (h : T ⊆ U) (n : ℕ) (ω : Forms k (Divisor G T) (n+1)) :
    radialize φ U n (pull (restrictDivisor G h) (n+1) ω) =
      pull (restrictDivisor G h) n (radialize φ T n ω) := by
  let π := restrictDivisor G h
  let D := weightedDivisorEuler (denominators G (T : Set (Fin 5))) φ
  let D' := weightedDivisorEuler (denominators G (U : Set (Fin 5))) φ
  change -interior n D'.liftKaehlerDifferential (pull π (n+1) ω) =
    pull π n (-interior n D.liftKaehlerDifferential ω)
  rw [map_neg]
  exact congrArg Neg.neg (CycleQ2LiteralThreefoldResidueContraction.interior_natural π.toRingHom
    (CycleQ2LogarithmicPullback.differential π) D.liftKaehlerDifferential D'.liftKaehlerDifferential
    (CycleQ2PoleReductionRadial.tangent_compatible π D D' (divisor_radial_restrict φ h)) n ω)
end Restriction

end CycleQ2ConeSimplexRadialClosure
end
#print axioms CycleQ2ConeSimplexRadialClosure.edge_on
#print axioms CycleQ2ConeSimplexRadialClosure.face_on
#print axioms CycleQ2ConeSimplexRadialClosure.tetrahedron_on
