import Proposal.GeometricConeLogClosure
import Proposal.GeometricConeSimplexExterior
import Proposal.GeometricConeSimplexNumerator
import Proposal.GeometricGradientSimplexFrame

/-! Local residues of the literal simple-pole cofactor numerators on the cone divisor. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2ConeSimplexClosure

open CycleQ2LogarithmicDifferential (exteriorD)
open CycleQ2ConeSimplexRings (Ambient Divisor embed quotient eqn coord normal)
open CycleQ2ConeSimplexNumerator (v e f v_field e_field f_field)
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (equation)
open MvPolynomial (pderiv)

variable {k : Type} [Field k] [CharZero k] (φ : CoeffRing →+* k)
local notation "G" => equation φ
variable (T : Finset (Fin 5)) (hT : ∀ i ∈ T, pderiv i G ≠ 0) (r : Fin 5) (hr : r ∈ T)

/-- Use the derivative indexed by r as normal on this simplex. This index
can be chosen independently of each face's normal when taking restrictions. -/
def chart : CycleQ2ConeLogClosure.Chart φ (Ambient G T) (Divisor G T) where
  embed := embed G T hT
  injective := CycleQ2ConeSimplexExterior.pull_embed_injective G T hT
  quotient := quotient G T
  equation := eqn G T
  equation_field := CycleQ2ConeSimplexRings.embed_polynomial G T hT G
  equation_zero := CycleQ2ConeSimplexRings.quotient_eqn G T
  normal := normal G hr
  normal_equation := CycleQ2ConeSimplexRings.normal_eqn G hr
  ambient := CycleQ2GradientSimplex.ambientBasis G (T : Set (Fin 5))
  x := coord G T
  ambient_exact := CycleQ2GradientSimplex.ambientBasis_apply G (T : Set (Fin 5))
  divisor := CycleQ2GradientSimplex.divisorBasis G (T : Set (Fin 5)) r hr
  y := fun j => quotient G T (coord G T (r.succAbove j))
  divisor_exact := CycleQ2GradientSimplex.divisorBasis_apply G (T : Set (Fin 5)) r hr

local notation "C" => chart φ T hT r hr

/-- Native divisor four-form at a vertex of the cone. -/
abbrev rv (i : Fin 5) (hi : i ∈ T) := C.res 4 (v φ T hT i hi)

/-- Native divisor three-form from the ambient edge. -/
abbrev re (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) := C.res 3 (e φ T hT i j hi hj)

/-- Native divisor two-form from the ambient face. -/
abbrev rf (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) :=
  C.res 2 (f φ T hT i j l hi hj hl)

local notation "V" => rv φ T hT r hr
local notation "E" => re φ T hT r hr
local notation "A" => rf φ T hT r hr

theorem vertex_on (i : Fin 5) (hi : i ∈ T) :
    C.Logarithmic 5 (v φ T hT i hi) ∧ exteriorD C.divisor 4 (V i hi) = 0 :=
  C.vertex i (hT i hi) _ (v_field φ T hT i hi)

theorem edge_on (i j : Fin 5) (hi : i ∈ T) (hj : j ∈ T) :
    C.Logarithmic 4 (e φ T hT i j hi hj) ∧
    exteriorD C.divisor 3 (E i j hi hj) = V i hi - V j hj :=
  C.edge i j (hT i hi) (hT j hj) _ _ _ (v_field φ T hT i hi)
    (v_field φ T hT j hj) (e_field φ T hT i j hi hj)

theorem face_on (i j l : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) :
    C.Logarithmic 3 (f φ T hT i j l hi hj hl) ∧
    exteriorD C.divisor 2 (A i j l hi hj hl) = E j l hj hl - E i l hi hl + E i j hi hj :=
  C.face i j l (hT i hi) (hT j hj) (hT l hl) _ _ _ _ (e_field φ T hT j l hj hl)
    (e_field φ T hT i l hi hl) (e_field φ T hT i j hi hj) (f_field φ T hT i j l hi hj hl)

theorem tetrahedron_on (i j l m : Fin 5) (hi : i ∈ T) (hj : j ∈ T) (hl : l ∈ T) (hm : m ∈ T) :
    A j l m hj hl hm-A i l m hi hl hm+A i j m hi hj hm-A i j l hi hj hl = 0 :=
  C.tetrahedron i j l m (hT i hi) (hT j hj) (hT l hl) _ _ _ _
    (f_field φ T hT j l m hj hl hm) (f_field φ T hT i l m hi hl hm)
    (f_field φ T hT i j m hi hj hm) (f_field φ T hT i j l hi hj hl)

end CycleQ2ConeSimplexClosure
end

#print axioms CycleQ2ConeSimplexClosure.vertex_on
#print axioms CycleQ2ConeSimplexClosure.edge_on
#print axioms CycleQ2ConeSimplexClosure.face_on
#print axioms CycleQ2ConeSimplexClosure.tetrahedron_on
