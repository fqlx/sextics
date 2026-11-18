import Proposal.GeometricLiteralThreefoldResidueContraction
import Proposal.ScratchLogIndexRealization

/-!
# Coordinate cofactor forms on regular cone charts

The signed single and double contractions of the five-coordinate volume
are defined over any commutative coefficient ring. Pulling the coordinate
frame to a second frame sends each cofactor to its counterpart there.
-/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2ConeSimplexCofactor

open CycleQ2GeometricExteriorSheaf (exteriorMap exteriorMap_wedge)
open CycleQ2LiteralThreefoldResidueContraction (interior interior_natural)

variable {k R S : Type} [CommRing k] [CommRing R] [CommRing S] [Algebra k R] [Algebra k S]

abbrev Frame (k R : Type) [CommRing k] [CommRing R] [Algebra k R] :=
  Module.Basis (Fin 5) R (KaehlerDifferential k R)

section Cofactors
variable (b : Frame k R)

/-- The ordered frame volume. -/
def volume : (⋀[R]^5 (KaehlerDifferential k R)) := exteriorPower.ιMulti R 5 b

/-- The scalar coefficient of the ordered five-form. -/
def top : R →ₗ[R] (⋀[R]^5 (KaehlerDifferential k R)) := (LinearMap.id : R →ₗ[R] R).smulRight (volume b)

/-- The four-form with signed single-deletion coefficients. -/
def flux : (Fin 5 → R) →ₗ[R] (⋀[R]^4 (KaehlerDifferential k R)) :=
  CycleQ2LogIndexRealization.vector (fun i => interior 4 (b.coord i) (volume b))

/-- The three-form with signed double-deletion coefficients in the strict upper triangle. -/
def biv : (Fin 5 → Fin 5 → R) →ₗ[R] (⋀[R]^3 (KaehlerDifferential k R)) :=
  CycleQ2LogIndexRealization.matrix (fun i j => interior 3 (b.coord i)
    (interior 4 (b.coord j) (volume b)))

end Cofactors

section Natural
variable (π : R →ₐ[k] S) (b : Frame k R) (c : Frame k S)
  {d : KaehlerDifferential k R →ₛₗ[π.toRingHom] KaehlerDifferential k S} (h : ∀ i, d (b i) = c i)
include h

private theorem coord_map (i : Fin 5) (x : KaehlerDifferential k R) :
    c.coord i (d x) = π (b.coord i x) := by
  have hx : x ∈ Submodule.span R (Set.range b) := by rw [b.span_eq]; trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨j,rfl⟩ := hx
    rw [h]
    by_cases e : j = i <;>
      simp [Module.Basis.coord_apply, Module.Basis.repr_self_apply, e]
  | zero => simp only [map_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]
  | smul r x _ hx => simp only [map_smulₛₗ, map_smul, RingHom.id_apply, hx, smul_eq_mul, map_mul]

private theorem volume_map :
    exteriorMap π.toRingHom d 5 (volume b) = volume c := by
  unfold volume
  rw [exteriorMap_wedge]
  exact congrArg (exteriorPower.ιMulti S 5) (funext h)

private theorem cofactor_map (n : ℕ) (i : Fin 5) (w : ⋀[R]^(n+1) (KaehlerDifferential k R)) :
    exteriorMap π.toRingHom d n (interior n (b.coord i) w) =
      interior n (c.coord i) (exteriorMap π.toRingHom d (n+1) w) :=
  (interior_natural π.toRingHom d (b.coord i) (c.coord i)
    (coord_map π b c h i) n w).symm

theorem top_map (v : R) :
    exteriorMap π.toRingHom d 5 (top b v) = top c (π v) := by
  change exteriorMap π.toRingHom d 5 (v • volume b) = π v • volume c
  rw [map_smulₛₗ, volume_map π b c h]

theorem flux_map (v : Fin 5 → R) :
    exteriorMap π.toRingHom d 4 (flux b v) = flux c (fun i => π (v i)) := by
  change exteriorMap π.toRingHom d 4
    (∑ i, v i • interior 4 (b.coord i) (volume b)) = _
  simp only [map_sum, map_smulₛₗ, cofactor_map π b c h, volume_map π b c h] <;> rfl

theorem biv_map (v : Fin 5 → Fin 5 → R) :
    exteriorMap π.toRingHom d 3 (biv b v) =
      biv c (fun i j => π (v i j)) := by
  change exteriorMap π.toRingHom d 3 (∑ i, ∑ j, v i j •
    (if i < j then interior 3 (b.coord i) (interior 4 (b.coord j) (volume b)) else 0)) =
      ∑ i, ∑ j, π (v i j) •
        (if i < j then interior 3 (c.coord i) (interior 4 (c.coord j) (volume c)) else 0)
  simp only [map_sum]
  refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
  by_cases hij : i < j <;>
    simp only [hij, if_pos, if_neg, smul_zero, map_zero, map_smulₛₗ,
      cofactor_map π b c h, volume_map π b c h]
end Natural

end CycleQ2ConeSimplexCofactor
end

#print axioms CycleQ2ConeSimplexCofactor.top_map
#print axioms CycleQ2ConeSimplexCofactor.flux_map
#print axioms CycleQ2ConeSimplexCofactor.biv_map
