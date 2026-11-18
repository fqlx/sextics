import Mathlib.Algebra.QuadraticAlgebra.Basic
import Proposal.GeometricGenericPencilLift

/-!
# The double cover of a weighted pencil fibre

Replacing the weight-two generator by the square of the last ordinary
generator gives a finite free quadratic algebra, including over the branch
divisor. Its sign-fixed elements are exactly the original weighted coordinate
ring.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2ProtectedPencilDoubleCover
open MvPolynomial

variable {K : Type} [Field K]
abbrev Poly (K : Type) [Field K] := MvPolynomial (Fin 5) K
abbrev Ring (g : Poly K) := Poly K ⧸ Ideal.span {g}
abbrev q (g : Poly K) := Ideal.Quotient.mkₐ K (Ideal.span {g})

def square : Poly K →ₐ[K] Poly K := aeval ![X 0, X 1, X 2, X 3, X 4 ^ 2]
def sign : Poly K →ₐ[K] Poly K := aeval ![X 0, X 1, X 2, X 3, -X 4]

theorem sign_square : (sign (K := K)).comp square = square := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [sign, square]

private theorem q_zero (g : Poly K) : q g g = 0 :=
  Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span (Set.mem_singleton _))

def descend {S : Type} [CommRing S] [Algebra K S] (g : Poly K)
    (f : Poly K →ₐ[K] S) (hf : f g = 0) : Ring g →ₐ[K] S :=
  Ideal.Quotient.liftₐ _ f (by
    intro p hp
    obtain ⟨b,rfl⟩ := Ideal.mem_span_singleton.mp hp
    simp [hf])

variable (g : Poly K)
abbrev B := Ring g
abbrev V := Ring (square g)
abbrev w : B g := q g (X 4)
abbrev u : V g := q (square g) (X 4)
abbrev Double := QuadraticAlgebra (B g) (w g) 0

def coverMap : B g →ₐ[K] V g :=
  descend g ((q (square g)).comp square) (q_zero _)

@[simp] theorem coverMap_q (p : Poly K) : coverMap g (q g p) = q (square g) (square p) := rfl

def beta : V g →ₐ[K] V g :=
  descend (square g) ((q (square g)).comp sign) (by
    change q (square g) (sign (square g)) = 0
    rw [show sign (square g) = square g from AlgHom.congr_fun sign_square g]
    exact q_zero _)

@[simp] theorem beta_q (p : Poly K) : beta g (q (square g) p) = q (square g) (sign p) := rfl

instance coverAlgebra : Algebra (B g) (V g) := (coverMap g).toRingHom.toAlgebra

instance coverTower : IsScalarTower K (B g) (V g) :=
  IsScalarTower.of_algebraMap_eq fun z => ((coverMap g).commutes z).symm

private abbrev scalar := IsScalarTower.toAlgHom K (B g) (Double g)
private abbrev base (i : Fin 5) : Double g := scalar g (q g (X i))

private def fromOrdinary : Poly K →ₐ[K] Double g :=
  aeval ![base g 0, base g 1, base g 2, base g 3, QuadraticAlgebra.omega]

private theorem fromOrdinary_square :
    (fromOrdinary g).comp square = (scalar g).comp (q g) := by
  apply MvPolynomial.algHom_ext
  intro i
  fin_cases i <;> simp [square, fromOrdinary, base, pow_two, QuadraticAlgebra.omega_mul_omega_eq_algebraMap] <;> rfl

def toDouble : V g →ₐ[K] Double g :=
  descend (square g) (fromOrdinary g) (by
    have h := AlgHom.congr_fun (fromOrdinary_square g) g
    exact h.trans (by simp only [AlgHom.comp_apply, q_zero, map_zero]))

theorem toDouble_coverMap (x : B g) : toDouble g (coverMap g x) = scalar g x := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact AlgHom.congr_fun (fromOrdinary_square g) p

def toDoubleOver : V g →ₐ[B g] Double g where
  __ := (toDouble g).toRingHom
  commutes' := toDouble_coverMap g

private theorem u_square : u g * u g = w g • (1 : V g) + (0 : B g) • u g := by
  change u g * u g = coverMap g (w g) * 1 + coverMap g 0 * u g
  rw [map_zero, zero_mul, add_zero, mul_one]
  change u g * u g = q (square g) (square (X 4))
  rw [show square (X 4 : Poly K) = X 4 ^ 2 by simp [square], map_pow, pow_two]

def fromDouble : Double g →ₐ[B g] V g :=
  QuadraticAlgebra.lift ⟨u g, u_square g⟩

private theorem fromDouble_omega : fromDouble g QuadraticAlgebra.omega = u g := by
  change coverMap g 0 * 1 + coverMap g 1 * u g = u g
  rw [map_zero, zero_mul, map_one, one_mul, zero_add]

private theorem fromDouble_base (i : Fin 5) :
    fromDouble g (base g i) = coverMap g (q g (X i)) :=
  (fromDouble g).commutes (q g (X i))

private theorem fromDouble_toDouble : (fromDouble g).comp (toDoubleOver g) = AlgHom.id (B g) (V g) := by
  apply AlgHom.ext
  intro x
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  have he : ((fromDouble g).restrictScalars K).comp (fromOrdinary g) = q (square g) := by
    apply MvPolynomial.algHom_ext
    intro i
    refine Fin.lastCases ?_ (fun j => ?_) i
    · change fromDouble g (fromOrdinary g (X 4)) = u g
      rw [show fromOrdinary g (X 4) = QuadraticAlgebra.omega by simp [fromOrdinary]]
      exact fromDouble_omega g
    · change fromDouble g (fromOrdinary g (X j.castSucc)) = q (square g) (X j.castSucc)
      have hb : fromOrdinary g (X j.castSucc) = base g j.castSucc := by
        fin_cases j <;> simp [fromOrdinary]
      have hs : square (X j.castSucc : Poly K) = X j.castSucc := by
        fin_cases j <;> simp [square]
      rw [hb, fromDouble_base, coverMap_q, hs]
  exact AlgHom.congr_fun he p

/-- The coordinate ring of the ordinary hypersurface is the rank-two algebra
obtained by adjoining the square root of the weighted coordinate. -/
def quadraticEquiv : V g ≃ₐ[B g] Double g :=
  AlgEquiv.ofAlgHom (toDoubleOver g) (fromDouble g) (by
    apply QuadraticAlgebra.algHom_ext
    change toDouble g (fromDouble g QuadraticAlgebra.omega) = QuadraticAlgebra.omega
    rw [fromDouble_omega]
    change fromOrdinary g (X 4) = _
    simp [fromOrdinary]) (fromDouble_toDouble g)

def coverBasis : Module.Basis (Fin 2) (B g) (V g) :=
  (QuadraticAlgebra.basis (w g) 0).map (quadraticEquiv g).symm.toLinearEquiv

theorem coverMap_injective : Function.Injective (coverMap g) := by
  intro x y h
  apply QuadraticAlgebra.algebraMap_injective (a := w g) (b := 0)
  exact (toDouble_coverMap g x).symm.trans ((congrArg (toDouble g) h).trans (toDouble_coverMap g y))

theorem beta_coverMap (x : B g) : beta g (coverMap g x) = coverMap g x := by
  obtain ⟨p,rfl⟩ := Ideal.Quotient.mk_surjective x
  exact congrArg (q (square g)) (AlgHom.congr_fun sign_square p)

theorem beta_u : beta g (u g) = -u g := by
  change q (square g) (sign (X 4)) = -q (square g) (X 4)
  rw [show sign (X 4 : Poly K) = -X 4 by simp [sign], map_neg]

private theorem fromDouble_coords (r s : B g) :
    fromDouble g ⟨r,s⟩ = coverMap g r + coverMap g s * u g := by
  change r • (1 : V g) + s • u g = _
  rw [← Algebra.algebraMap_eq_smul_one, Algebra.smul_def]
  rfl

private theorem beta_fromDouble (r s : B g) :
    beta g (fromDouble g ⟨r,s⟩) = fromDouble g ⟨r,-s⟩ := by
  rw [fromDouble_coords, fromDouble_coords, map_add, map_mul, beta_u, beta_coverMap, beta_coverMap, map_neg]
  ring

variable [CharZero K]

/-- Coefficients of odd powers have the sign character. In characteristic
zero a fixed element has a unique expression from the weighted coordinate ring. -/
theorem beta_fixed_iff (v : V g) : beta g v = v ↔ ∃! b : B g, coverMap g b = v := by
  constructor
  · obtain ⟨⟨r,s⟩,rfl⟩ := (quadraticEquiv g).symm.surjective v
    change beta g (fromDouble g ⟨r,s⟩) = fromDouble g ⟨r,s⟩ → _
    intro h
    rw [beta_fromDouble] at h
    have hs : -s = s :=
      congrArg QuadraticAlgebra.im ((quadraticEquiv g).symm.injective h)
    have hz : (2 : K) • s = 0 := by
      rw [show (2 : K) = 1 + 1 by norm_num, add_smul, one_smul]
      exact neg_eq_iff_add_eq_zero.mp hs
    have hs0 : s = 0 := (smul_eq_zero.mp hz).resolve_left (by norm_num)
    subst s
    have he : fromDouble g ⟨r,0⟩ = coverMap g r := by simp [fromDouble_coords]
    exact ⟨r, he.symm, fun y hy => coverMap_injective g (hy.trans he)⟩
  · rintro ⟨b,rfl,_⟩
    exact beta_coverMap g b

end CycleQ2ProtectedPencilDoubleCover
end

#print axioms CycleQ2ProtectedPencilDoubleCover.quadraticEquiv
#print axioms CycleQ2ProtectedPencilDoubleCover.coverBasis

#print axioms CycleQ2ProtectedPencilDoubleCover.beta_fixed_iff
