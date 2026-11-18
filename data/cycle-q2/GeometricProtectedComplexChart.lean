import Proposal.GeometricComplexProjectiveChart
import Proposal.GeometricFormalInputs03Part01
import Mathlib.Topology.Algebra.MvPolynomial
import Mathlib.Topology.Category.TopCat.Basic

/-!
# The protected sextic and its standard affine chart over the complex numbers

The complex projective hypersurface is cut out by the protected polynomial
on lines in complex six-space. At a point of the dehomogenized affine
hypersurface, its chart inclusion is given by homogeneous coordinates
`[1:v]`. Composition with the inclusion in complex projective five-space
factors through the entire affine five-space.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
namespace CycleQ2ProtectedComplexChart

open CategoryTheory MvPolynomial CycleQ2ComplexProjectiveChart
open scoped CycleQ2ComplexProjectiveChart

/-- The protected sextic scales by the sixth power on vectors. -/
theorem eval_F_smul (c : ℂ) (v : CycleQ2ComplexProjectiveChart.Vector) :
    eval (c • v) HodgeSubmission.F = c ^ 6 * eval v HodgeSubmission.F := by
  simp [HodgeSubmission.F, Pi.smul_apply, smul_eq_mul]
  ring

/-- Vanishing of the protected sextic descends to the projective line
represented by any nonzero vector. -/
def projectiveZeroLocus : Set Projective :=
  Projectivization.lift (fun v : {v : CycleQ2ComplexProjectiveChart.Vector // v ≠ 0} => eval v.val HodgeSubmission.F = 0)
    (by
      intro a b t ht
      have h : t ≠ 0 := fun he => a.property (by simpa [he] using ht)
      exact propext (by rw [ht, eval_F_smul, mul_eq_zero, or_iff_right (pow_ne_zero _ h)]))

@[simp] theorem mk_mem_projectiveZeroLocus (v : CycleQ2ComplexProjectiveChart.Vector) (hv : v ≠ 0) :
    Projectivization.mk ℂ v hv ∈ projectiveZeroLocus ↔ eval v HodgeSubmission.F = 0 := Iff.rfl

/-- The points of the actual dehomogenized chart in the affine complex topology. -/
def affineZeroLocus : Set Affine := {v | eval v CycleQ2AffineClearing.affineF = 0}

/-- Evaluation after dehomogenizing agrees with substitution of the vector
with initial coordinate one. -/
theorem eval_dehomogenize (v : Affine) (P : HodgeComputer.AmbientPoly 5) :
    eval v (CycleQ2AffineChart.dehomogenize P) = eval (homogenize v) P := by
  change aeval v (aeval (Fin.cases 1 X) P) = aeval (homogenize v) P
  have h : (fun i : Fin 6 => aeval v (Fin.cases (1 : HodgeComputer.AmbientPoly 4) X i)) =
      homogenize v := by
    funext i
    refine Fin.cases (by simp [homogenize]) (fun j => by simp [homogenize]) i
  rw [comp_aeval_apply, h]

theorem chartMap_mem_iff (v : Affine) :
    chartMap v ∈ projectiveZeroLocus ↔ v ∈ affineZeroLocus := by
  change eval (homogenize v) HodgeSubmission.F = 0 ↔
    eval v (CycleQ2AffineChart.dehomogenize HodgeSubmission.F) = 0
  rw [eval_dehomogenize]

theorem affineZeroLocus_isClosed : IsClosed affineZeroLocus :=
  isClosed_eq (continuous_eval CycleQ2AffineClearing.affineF) continuous_const

theorem projectiveZeroLocus_isClosed : IsClosed projectiveZeroLocus := by
  apply isQuotientMap_mk.isClosed_preimage.mp
  exact isClosed_eq ((continuous_eval HodgeSubmission.F).comp continuous_subtype_val)
    continuous_const

abbrev AffineSpace : TopCat := TopCat.of Affine
abbrev ProjectiveSpace : TopCat := TopCat.of Projective
abbrev AffineHypersurface : TopCat := TopCat.of affineZeroLocus
abbrev ProjectiveHypersurface : TopCat := TopCat.of projectiveZeroLocus

def affineInclusion : AffineHypersurface ⟶ AffineSpace :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def projectiveInclusion : ProjectiveHypersurface ⟶ ProjectiveSpace :=
  TopCat.ofHom ⟨Subtype.val, continuous_subtype_val⟩

def affineChart : AffineSpace ⟶ ProjectiveSpace :=
  TopCat.ofHom ⟨chartMap, continuous_chartMap⟩

def chartInclusion : AffineHypersurface ⟶ ProjectiveHypersurface :=
  TopCat.ofHom ⟨(fun v => ⟨chartMap v.val, (chartMap_mem_iff v.val).mpr v.property⟩),
    (continuous_chartMap.comp continuous_subtype_val).subtype_mk _⟩

/-- The image is exactly the first standard open of the protected projective hypersurface. -/
theorem chartInclusion_range :
    Set.range chartInclusion = projectiveInclusion ⁻¹' chartDomain := by
  ext p
  constructor
  · rintro ⟨v, rfl⟩
    exact one_ne_zero
  · intro hp
    have hi := chartMap_dehomogenize p.val hp
    have hz : dehomogenize p.val ∈ affineZeroLocus :=
      (chartMap_mem_iff _).mp (by rw [hi]; exact p.property)
    exact ⟨⟨dehomogenize p.val, hz⟩, Subtype.ext hi⟩

theorem chartInclusion_isOpenEmbedding : Topology.IsOpenEmbedding chartInclusion := by
  constructor
  · apply Topology.IsEmbedding.of_comp chartInclusion.hom.continuous projectiveInclusion.hom.continuous
    have hChart : Topology.IsEmbedding chartMap :=
      Topology.IsEmbedding.subtypeVal.comp chartHomeomorph.isEmbedding
    exact hChart.comp Topology.IsEmbedding.subtypeVal
  · rw [chartInclusion_range]
    exact isOpen_chartDomain.preimage projectiveInclusion.hom.continuous

theorem chart_factorization :
    chartInclusion ≫ projectiveInclusion = affineInclusion ≫ affineChart := rfl

end CycleQ2ProtectedComplexChart
end

#print axioms CycleQ2ProtectedComplexChart.chartMap_mem_iff
#print axioms CycleQ2ProtectedComplexChart.chartInclusion_isOpenEmbedding
#print axioms CycleQ2ProtectedComplexChart.chart_factorization
