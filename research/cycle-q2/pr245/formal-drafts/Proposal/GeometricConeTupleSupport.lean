import Proposal.GeometricGradientSimplexFrame

/-! Supports and exact frames for the ordered cone derivative simplices. -/
set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2ConeSimplexCochain
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricHodgeThreefold (equation)

/-- The first normal of an ordered simplex is also available on degenerate
tuples or on intersections whose localized ring is zero. -/
def support {n : ℕ} (x : Fin n → Fin 5) : Finset (Fin 5) := Finset.univ.image x

theorem mem_support {n : ℕ} (x : Fin n → Fin 5) (a : Fin n) : x a ∈ support x :=
  Finset.mem_image_of_mem x (Finset.mem_univ a)

theorem support_mono {n m : ℕ} (x : Fin n → Fin 5) (u : Fin m → Fin n) :
    support (x ∘ u) ⊆ support x := by
  intro i hi
  obtain ⟨a,_,rfl⟩ := Finset.mem_image.mp hi
  exact mem_support x (u a)

abbrev tupleBasis {A : Type} [CommRing A] (ψ : CoeffRing →+* A) {n : ℕ}
    (x : Fin (n+1) → Fin 5) :=
  CycleQ2GradientSimplex.divisorBasis (equation ψ) (support x : Set (Fin 5)) (x 0) (mem_support x 0)

end CycleQ2ConeSimplexCochain
end
