import Mathlib.AlgebraicGeometry.AffineScheme

/-! Affine open subsets subordinate to any open cover form a basis. -/

set_option autoImplicit false
open AlgebraicGeometry TopologicalSpace

namespace CycleQ2.Cech

universe u v
variable {X : Scheme.{u}} {ι : Type v} (U : ι → X.Opens)

/-- An affine open lying in one member of the given cover. -/
def SubordinateAffine (V : X.Opens) : Prop := IsAffineOpen V ∧ ∃ i, V ≤ U i

theorem isBasis_subordinateAffine (hc : (⨆ i, U i) = ⊤) :
    Opens.IsBasis {V | SubordinateAffine U V} := by
  apply Opens.isBasis_iff_nbhd.mpr
  intro W x hx
  have hxt : x ∈ ⨆ i, U i := by rw [hc]; exact Opens.mem_top _
  obtain ⟨i, hi⟩ := Opens.mem_iSup.mp hxt
  obtain ⟨V, hV, hxV, hle⟩ := Opens.isBasis_iff_nbhd.mp X.isBasis_affineOpens
    (show x ∈ W ⊓ U i from ⟨hx, hi⟩)
  exact ⟨V, ⟨hV, i, hle.trans inf_le_right⟩, hxV, hle.trans inf_le_left⟩

end CycleQ2.Cech

#print axioms CycleQ2.Cech.isBasis_subordinateAffine
