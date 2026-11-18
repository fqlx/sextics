import Mathlib.AlgebraicGeometry.Properties
import Mathlib.RingTheory.Spectrum.Prime.Topology

/-!
# Global dimension from affine dimension bounds

Every finite chain of irreducible closed sets in a scheme is represented by
a chain of generic points. An affine neighborhood of the most specialized
point contains the entire chain, with the same strict specialization relations.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2AffineChartDimensionBound

open AlgebraicGeometry TopologicalSpace Order
open scoped ENat

/-- A uniform bound on the dimensions of affine opens bounds the dimension
of the scheme, including the case of the empty scheme. -/
theorem topologicalKrullDim_le (X : Scheme) (n : WithBot ℕ∞)
    (bound : ∀ U : X.Opens, IsAffineOpen U → ringKrullDim Γ(X,U) ≤ n) :
    topologicalKrullDim X ≤ n := by
  change (⨆ p : LTSeries (IrreducibleCloseds X), (p.length : WithBot ℕ∞)) ≤ n
  apply iSup_le
  intro p
  let : PartialOrder X := specializationOrder X
  let e : IrreducibleCloseds X ≃o X := irreducibleSetEquivPoints
  let y (i : Fin (p.length + 1)) : X := e (p i)
  have hyst : StrictMono y := e.strictMono.comp p.strictMono
  obtain ⟨_, ⟨V,hV,rfl⟩,hx,_⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (y 0)) isOpen_univ
  let W : X.Opens := V
  have hy (i : Fin (p.length + 1)) : y i ∈ W := by
    have hspec : y i ⤳ y 0 := hyst.monotone (Fin.zero_le i)
    exact hspec.mem_open W.isOpen hx
  let : PartialOrder W.toScheme := specializationOrder W.toScheme
  let z (i : Fin (p.length + 1)) : W.toScheme := ⟨y i,hy i⟩
  have hzt : StrictMono z := by
    intro i j hij
    obtain ⟨hf, hb⟩ := hyst hij
    change (z j ⤳ z i) ∧ ¬ (z i ⤳ z j)
    exact ⟨W.ι.isOpenEmbedding.isInducing.specializes_iff.mp hf,
      fun h => hb (W.ι.isOpenEmbedding.isInducing.specializes_iff.mpr h)⟩
  let eV : IrreducibleCloseds W.toScheme ≃o W.toScheme := irreducibleSetEquivPoints
  let q := LTSeries.mk p.length (eV.symm ∘ z) (eV.symm.strictMono.comp hzt)
  calc
    _ ≤ topologicalKrullDim W.toScheme := q.length_le_krullDim
    _ = topologicalKrullDim (Spec Γ(X,W)) :=
      IsHomeomorph.topologicalKrullDim_eq _ hV.isoSpec.hom.homeomorph.isHomeomorph
    _ = ringKrullDim Γ(X,W) := PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ ≤ n := bound W hV

#print axioms topologicalKrullDim_le
end CycleQ2AffineChartDimensionBound
end
