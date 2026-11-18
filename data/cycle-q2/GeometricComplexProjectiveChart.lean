import Mathlib.LinearAlgebra.Projectivization.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Homeomorph.Defs

/-!
# The first affine chart of complex projective five-space

Nonzero vectors give projective space its quotient topology. On the open
where coordinate zero is nonzero, division by that coordinate gives the
continuous inverse to the map `v ↦ [1 : v]`.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ComplexProjectiveChart

abbrev Affine := Fin 5 → ℂ
abbrev Vector := Fin 6 → ℂ
abbrev Projective := Projectivization ℂ Vector

/-- The quotient topology from the space of nonzero complex vectors. -/
scoped instance projectiveTopology : TopologicalSpace Projective :=
  TopologicalSpace.coinduced (Projectivization.mk' ℂ) inferInstance

theorem isQuotientMap_mk :
    Topology.IsQuotientMap (Projectivization.mk' ℂ (V := Vector)) :=
  ⟨⟨rfl⟩, fun p => ⟨⟨p.rep, p.rep_nonzero⟩, p.mk_rep⟩⟩

/-- Homogeneous coordinates on the first affine chart. -/
def homogenize (v : Affine) : Vector := Fin.cons 1 v

@[simp] theorem homogenize_zero (v : Affine) : homogenize v 0 = 1 := rfl

@[simp] theorem homogenize_succ (v : Affine) (i : Fin 5) : homogenize v i.succ = v i := by
  simp [homogenize]

theorem homogenize_ne_zero (v : Affine) : homogenize v ≠ 0 :=
  fun h => one_ne_zero (congrFun h 0)

theorem continuous_homogenize : Continuous homogenize := by
  apply continuous_pi
  intro i
  refine Fin.cases ?_ (fun j => ?_) i
  · exact continuous_const
  · simpa only [homogenize_succ] using (continuous_apply j : Continuous (fun v : Affine => v j))

def chartMap (v : Affine) : Projective :=
  Projectivization.mk ℂ (homogenize v) (homogenize_ne_zero v)

theorem continuous_chartMap : Continuous chartMap :=
  isQuotientMap_mk.continuous.comp (continuous_homogenize.subtype_mk homogenize_ne_zero)

/-- The open chart where the first homogeneous coordinate is nonzero. -/
def chartDomain : Set Projective := Projectivization.lift (fun v => v.val 0 ≠ 0) (by
  intro a b t h
  have ht : t ≠ 0 := fun e => a.property (by simpa [e] using h)
  exact propext (by simp [h, Pi.smul_apply, smul_eq_mul, ht]))

@[simp] theorem mk_mem_chartDomain (v : Vector) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ chartDomain ↔ v 0 ≠ 0 := Iff.rfl

theorem isOpen_chartDomain : IsOpen chartDomain := by
  apply isQuotientMap_mk.isOpen_preimage.mp
  exact isOpen_ne_fun ((continuous_apply 0).comp continuous_subtype_val) continuous_const

/-- The five coordinate ratios on the chart. -/
def dehomogenize : Projective → Affine := Projectivization.lift
  (fun v i => v.val i.succ / v.val 0) (by
    intro a b t h
    have ht : t ≠ 0 := fun e => a.property (by simpa [e] using h)
    ext i
    simp only [h, Pi.smul_apply, smul_eq_mul, mul_div_mul_left _ _ ht])

@[simp] theorem dehomogenize_mk (v : Vector) (hv : v ≠ 0) (i : Fin 5) :
    dehomogenize (Projectivization.mk ℂ v hv) i = v i.succ / v 0 := rfl

theorem continuousOn_dehomogenize : ContinuousOn dehomogenize chartDomain := by
  apply (isQuotientMap_mk.continuousOn_isOpen_iff isOpen_chartDomain).2
  apply continuousOn_pi.2
  intro i
  exact ((continuous_apply i.succ).comp continuous_subtype_val).continuousOn.div
    ((continuous_apply 0).comp continuous_subtype_val).continuousOn (fun _ h => h)

@[simp] theorem dehomogenize_chartMap (v : Affine) : dehomogenize (chartMap v) = v := by
  ext i
  simp [chartMap]

theorem chartMap_dehomogenize (p : Projective) (hp : p ∈ chartDomain) :
    chartMap (dehomogenize p) = p := by
  induction p using Projectivization.ind with
  | h v hv =>
    have h0 : v 0 ≠ 0 := hp
    apply (Projectivization.mk_eq_mk_iff' ℂ _ _ _ _).2
    refine ⟨(v 0)⁻¹, ?_⟩
    funext i
    refine Fin.cases ?_ (fun j => ?_) i
    · simp [Pi.smul_apply, smul_eq_mul, h0]
    · simp [Pi.smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm]

/-- Complex affine five-space is homeomorphic to this standard open in
complex projective five-space. -/
def chartHomeomorph : Affine ≃ₜ chartDomain where
  toFun v := ⟨chartMap v, one_ne_zero⟩
  invFun p := dehomogenize p.val
  left_inv := dehomogenize_chartMap
  right_inv p := Subtype.ext (chartMap_dehomogenize _ p.property)
  continuous_toFun := continuous_chartMap.subtype_mk _
  continuous_invFun := continuousOn_iff_continuous_domRestrict.mp continuousOn_dehomogenize

#print axioms chartHomeomorph

end CycleQ2ComplexProjectiveChart
