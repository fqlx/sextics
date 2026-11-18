import Proposal.ScratchCechSubordinateAffineBasis
import Proposal.ScratchWeightedIntersectionFrame

/-! The finite gradient cover of the native weighted hypersurface admits a
basis of affine opens with three exact local coordinates. -/

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry Module TopologicalSpace CycleQ2.Cech.Sections
open CycleQ2WeightedResidueAtlas CycleQ2GeometricHodgeThreefold CycleQ2GenericSexticGradient
open scoped KaehlerDifferential

namespace CycleQ2.Cech.WeightedBasis

variable {k : Type} [CommRing k] (φ : CoeffRing →+* k)

abbrev Good (V : (threefold φ).Opens) := SubordinateAffine (U φ) V

theorem isBasis (hg : IsUnit (φ goodParameter)) :
    Opens.IsBasis {V | Good φ V} :=
  isBasis_subordinateAffine (U φ) (cover φ hg)

theorem frame {V : (threefold φ).Opens} (hV : Good φ V) :
    letI := algebra (toBase φ) V
    ∃ (x : Fin 3 → Γ(threefold φ,V)) (b : Basis (Fin 3) Γ(threefold φ,V) Ω[Γ(threefold φ,V)⁄k]),
      ∀ i, b i = KaehlerDifferential.D k _ (x i) := by
  obtain ⟨hA, a, hle⟩ := hV
  exact CycleQ2WeightedIntersectionFrame.exact_frame φ a hA hle

theorem good_vertex (a : Index) : Good φ (U φ a) := ⟨affine φ a, a, le_rfl⟩

theorem good_intersection {I : Type*} [Finite I] [Nonempty I] (v : I → Index) :
    Good φ (⨅ i, U φ (v i)) :=
  let i : I := Classical.choice inferInstance
  ⟨finite_affine φ v, v i, iInf_le _ i⟩

end CycleQ2.Cech.WeightedBasis
end

#print axioms CycleQ2.Cech.WeightedBasis.isBasis
#print axioms CycleQ2.Cech.WeightedBasis.frame
