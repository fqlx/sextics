import Proposal.GeometricSquareZeroReducedCotangent
import Mathlib.LinearAlgebra.ExteriorPower.Basic
import Mathlib.LinearAlgebra.Alternating.Curry
import Mathlib.Tactic.FinCases

/-!
# The two-equation adjunction numerator in a one-parameter curve family

The order of the conormal factors is the surface equation followed by the
curve equation. Changing both conormals multiplies the numerator by their
two-by-two determinant. Evaluating on a surface conormal wedge gives the
negative of the surface velocity times the relative numerator, independently
of the velocity of the second equation.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
noncomputable section

namespace CycleQ2CurveCylinderAdjunction

variable {R E : Type*} [CommRing R] [AddCommGroup E] [Module R E]

/-- Wedge two equation differentials onto a two-form in the ambient module. -/
def adjunctionNumerator (h g : E) : (⋀[R]^2 E) →ₗ[R] (⋀[R]^4 E) :=
  exteriorPower.alternatingMapLinearEquiv
    (((exteriorPower.ιMulti R 4).curryLeft h).curryLeft g)

theorem adjunctionNumerator_wedge (h g a b : E) :
    adjunctionNumerator (R := R) h g (exteriorPower.ιMulti R 2 ![a, b]) =
      exteriorPower.ιMulti R 4 ![h, g, a, b] := by
  rw [adjunctionNumerator, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
  rfl

private theorem add_second (h u v a b : E) :
    exteriorPower.ιMulti R 4 ![h, u + v, a, b] =
      exteriorPower.ιMulti R 4 ![h, u, a, b] + exteriorPower.ιMulti R 4 ![h, v, a, b] :=
  ((exteriorPower.ιMulti R 4).curryLeft h).map_vecCons_add ![a, b] u v

private theorem smul_second (h u a b : E) (c : R) :
    exteriorPower.ιMulti R 4 ![h, c • u, a, b] = c • exteriorPower.ιMulti R 4 ![h, u, a, b] :=
  ((exteriorPower.ιMulti R 4).curryLeft h).map_vecCons_smul ![a, b] c u

private theorem swap_first (x y a b : E) :
    exteriorPower.ιMulti R 4 ![y, x, a, b] = -exteriorPower.ιMulti R 4 ![x, y, a, b] := by
  have e : ![y, x, a, b] = ![x, y, a, b] ∘ Equiv.swap (0 : Fin 4) 1 := by
    funext i
    fin_cases i <;> rfl
  rw [e, AlternatingMap.map_swap _ _ (by decide)]

private theorem swap_middle (x y a b : E) :
    exteriorPower.ιMulti R 4 ![x, a, y, b] = -exteriorPower.ιMulti R 4 ![x, y, a, b] := by
  have e : ![x, a, y, b] = ![x, y, a, b] ∘ Equiv.swap (1 : Fin 4) 2 := by
    funext i
    fin_cases i <;> rfl
  rw [e, AlternatingMap.map_swap _ _ (by decide)]

/-- The absolute numerator changes by the determinant of a change of the two
defining equations, for every ambient two-form. -/
theorem adjunctionNumerator_change (h g : E) (a b c d : R) :
    adjunctionNumerator (a • h + b • g) (c • h + d • g) =
      (a * d - b * c) • adjunctionNumerator (R := R) h g := by
  apply exteriorPower.linearMap_ext
  apply AlternatingMap.ext
  intro v
  change adjunctionNumerator _ _ (exteriorPower.ιMulti R 2 v) =
    (a * d - b * c) • adjunctionNumerator _ _ (exteriorPower.ιMulti R 2 v)
  have hv : v = ![v 0, v 1] := by funext i; fin_cases i <;> rfl
  rw [hv, adjunctionNumerator_wedge, adjunctionNumerator_wedge]
  simp only [AlternatingMap.map_vecCons_add, AlternatingMap.map_vecCons_smul, add_second,
    smul_second, smul_add, smul_smul]
  have hz (x : E) : exteriorPower.ιMulti R 4 ![x, x, v 0, v 1] = 0 :=
    (exteriorPower.ιMulti R 4).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  rw [hz, hz, smul_zero, smul_zero, zero_add, add_zero, swap_first (R := R) h g,
    smul_neg, ← sub_eq_add_neg]
  exact (sub_smul (a*d) (b*c) (exteriorPower.ιMulti R 4 ![h, g, v 0, v 1])).symm

/-- With base differential first, the mixed coefficient on a conormal wedge
is minus the first equation velocity. The second equation velocity cancels. -/
theorem moving_conormal_numerator (dt h g β : E) (L M : R) :
    adjunctionNumerator (h + L • dt) (g + M • dt) (exteriorPower.ιMulti R 2 ![h, β]) =
      (-L) • exteriorPower.ιMulti R 4 ![dt, h, g, β] := by
  rw [adjunctionNumerator_wedge, AlternatingMap.map_vecCons_add, AlternatingMap.map_vecCons_smul]
  have hh : exteriorPower.ιMulti R 4 ![h, g + M • dt, h, β] = 0 :=
    (exteriorPower.ιMulti R 4).map_eq_zero_of_eq _ (i := 0) (j := 2) rfl (by decide)
  have ht : exteriorPower.ιMulti R 4 ![dt, dt, h, β] = 0 :=
    (exteriorPower.ιMulti R 4).map_eq_zero_of_eq _ (i := 0) (j := 1) rfl (by decide)
  rw [hh, zero_add, add_second, smul_second, ht, smul_zero, add_zero,
    swap_middle (R := R) dt h g β, smul_neg]
  exact (neg_smul L _).symm

/-- The fibre one-forms are represented by ambient forms modulo the base and
the two local defining equation differentials. -/
def fibreConormals (dt h g : E) : Submodule R E :=
  Submodule.span R {dt, h, g}

private def relativeNumerator (dt h g : E) : E →ₗ[R] ⋀[R]^4 E where
  toFun β := exteriorPower.ιMulti R 4 ![dt, h, g, β]
  map_add' x y :=
    ((((exteriorPower.ιMulti R 4).curryLeft dt).curryLeft h).curryLeft g).map_vecCons_add ![] x y
  map_smul' c x :=
    ((((exteriorPower.ιMulti R 4).curryLeft dt).curryLeft h).curryLeft g).map_vecCons_smul ![] c x

/-- The relative adjunction numerator on the quotient cotangent presentation.
This construction only uses exterior algebra and also works at a singular
point of the curve. -/
def fibreNumerator (dt h g : E) : (E ⧸ fibreConormals (R := R) dt h g) →ₗ[R] ⋀[R]^4 E :=
  (fibreConormals (R := R) dt h g).liftQ (relativeNumerator dt h g) (by
    apply Submodule.span_le.mpr
    intro x hx
    rcases hx with rfl | rfl | hx
    · exact (exteriorPower.ιMulti R 4).map_eq_zero_of_eq _ (i := 0) (j := 3) rfl (by decide)
    · exact (exteriorPower.ιMulti R 4).map_eq_zero_of_eq _ (i := 1) (j := 3) rfl (by decide)
    · obtain rfl := Set.mem_singleton_iff.mp hx
      exact (exteriorPower.ιMulti R 4).map_eq_zero_of_eq _ (i := 2) (j := 3) rfl (by decide))

theorem fibreNumerator_mk (dt h g β : E) :
    fibreNumerator (R := R) dt h g ((fibreConormals (R := R) dt h g).mkQ β) =
      exteriorPower.ιMulti R 4 ![dt, h, g, β] := rfl

theorem moving_conormal_on_fibre (dt h g β : E) (L M : R) :
    adjunctionNumerator (h + L • dt) (g + M • dt) (exteriorPower.ιMulti R 2 ![h, β]) =
      (-L) • fibreNumerator (R := R) dt h g ((fibreConormals (R := R) dt h g).mkQ β) :=
  moving_conormal_numerator dt h g β L M

section Cotangent

open CycleQ2GeometricSquareZeroReducedCotangent

variable {K P A : Type*} [CommRing K] [CommRing P] [CommRing A]
    [Algebra K P] [Algebra P A] [Algebra K A] [IsScalarTower K P A]

local notation "δ" => reducedUniversal (K := K) (E := P) (C := A)

/-- The original differential of a varying equation in the ambient
cotangent module restricted to the closed chart. -/
theorem reducedUniversal_velocity (e f v : P) (he : algebraMap P A e = 0) :
    δ (f + e * v) = δ f + algebraMap P A v • δ e := by
  rw [map_add, Derivation.leibniz, thick_smul (K := K) e, thick_smul (K := K) v, he, zero_smul,
    zero_add]

/-- The mixed wedge calculation in the actual base-changed ambient cotangent
module. Only the vanishing of the parameter on the closed chart is required. -/
theorem varying_equations_restricted (e f g l m : P) (he : algebraMap P A e = 0)
    (β : ReducedCotangent (K := K) (E := P) (C := A)) :
    adjunctionNumerator (R := A) (δ (f + e * l)) (δ (g + e * m))
      (exteriorPower.ιMulti A 2 ![δ f, β]) =
      -(algebraMap P A l) • fibreNumerator (R := A) (δ e) (δ f) (δ g)
        ((fibreConormals (R := A) (δ e) (δ f) (δ g)).mkQ β) := by
  rw [reducedUniversal_velocity (K := K) e f l he, reducedUniversal_velocity (K := K) e g m he]
  exact moving_conormal_on_fibre (δ e) (δ f) (δ g) β _ _

private theorem reducedUniversal_combination (a b f g : P) (hf : algebraMap P A f = 0)
    (hg : algebraMap P A g = 0) :
    δ (a * f + b * g) = algebraMap P A a • δ f + algebraMap P A b • δ g := by
  rw [map_add, Derivation.leibniz, Derivation.leibniz, thick_smul (K := K) f,
    thick_smul (K := K) g, thick_smul (K := K) a, thick_smul (K := K) b, hf, hg,
    zero_smul, zero_smul, add_zero, add_zero]

/-- Changing the original equations by polynomial coefficients changes the
restricted adjunction numerator by the specialization of their determinant. -/
theorem restricted_equations_change (a b c d f g : P) (hf : algebraMap P A f = 0)
    (hg : algebraMap P A g = 0) :
    adjunctionNumerator (R := A) (δ (a*f + b*g)) (δ (c*f + d*g)) =
      algebraMap P A (a*d - b*c) • adjunctionNumerator (R := A) (δ f) (δ g) := by
  rw [reducedUniversal_combination a b f g hf hg, reducedUniversal_combination c d f g hf hg,
    map_sub, map_mul, map_mul]
  exact adjunctionNumerator_change (δ f) (δ g) _ _ _ _

end Cotangent

end CycleQ2CurveCylinderAdjunction
end

#print axioms CycleQ2CurveCylinderAdjunction.adjunctionNumerator_change
#print axioms CycleQ2CurveCylinderAdjunction.moving_conormal_numerator

#print axioms CycleQ2CurveCylinderAdjunction.moving_conormal_on_fibre

#print axioms CycleQ2CurveCylinderAdjunction.varying_equations_restricted

#print axioms CycleQ2CurveCylinderAdjunction.restricted_equations_change
