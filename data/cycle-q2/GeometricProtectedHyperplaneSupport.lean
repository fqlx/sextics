import Proposal.GeometricProtectedComplexPrincipalOpen
import Proposal.GeometricExistence
import Mathlib.Analysis.Convex.Contractible
import Mathlib.AlgebraicTopology.SingularHomology.HomotopyInvariance
import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Category.ModuleCat.Limits
import Mathlib.CategoryTheory.Abelian.Opposite
import Mathlib.Analysis.Complex.Basic

/-!
# Ambient singular cohomology on the protected sextic's affine chart

We use complex-valued singular cochains on the complex points. The inclusion
of the affine sextic chart into projective space passes through affine
five-space. Its contraction kills every ambient class of positive degree.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false

noncomputable section
open AlgebraicTopology CategoryTheory CategoryTheory.Limits Opposite
namespace CycleQ2ProtectedHyperplaneSupport

/-- Complex-valued singular cohomology. Passing to the opposite module category turns
the singular simplicial chains into the product of scalar cochains on the simplices. -/
def betti (n : ℕ) : TopCat.{0}ᵒᵖ ⥤ ModuleCat.{0} ℂ :=
  ((singularHomologyFunctor (ModuleCat.{0} ℂ)ᵒᵖ n).obj (op (ModuleCat.of ℂ ℂ))).leftOp

universe w v u

/-- In positive degrees, singular homology of a contractible space vanishes with
any coefficients admitting the chain complex and its homology. -/
theorem isZero_of_contractible (C : Type u) [Category.{v} C] [Preadditive C]
    [HasCoproducts.{w} C] [CategoryWithHomology C] (R : C) (X : TopCat.{w})
    [ContractibleSpace X] (n : ℕ) (hn : n ≠ 0) :
    IsZero (((singularHomologyFunctor C n).obj R).obj X) := by
  obtain ⟨x, ⟨h⟩⟩ := id_nullhomotopic X
  let P := TopCat.of PUnit.{w+1}
  let f : X ⟶ P := TopCat.ofHom (ContinuousMap.const _ PUnit.unit)
  let g : P ⟶ X := TopCat.ofHom (ContinuousMap.const _ x)
  let F := (singularHomologyFunctor C n).obj R
  have H : TopCat.Homotopy (𝟙 X) (f ≫ g) := h
  have hmap : F.map (𝟙 X) = F.map (f ≫ g) :=
    H.congr_homologyMap_singularChainComplexFunctor R n
  have hP : IsZero (F.obj P) :=
    isZero_singularHomologyFunctor_of_totallyDisconnectedSpace C n R P hn
  rw [IsZero.iff_id_eq_zero]
  change 𝟙 (F.obj X) = 0
  rw [← F.map_id, hmap, F.map_comp, hP.eq_zero_of_src (F.map g), comp_zero]

abbrev Betti (n : ℕ) (X : TopCat.{0}) := (betti n).obj (op X)

def restrict {X Y : TopCat.{0}} (n : ℕ) (f : X ⟶ Y) : Betti n Y →ₗ[ℂ] Betti n X :=
  ((betti n).map f.op).hom

theorem restrict_comp {X Y Z : TopCat.{0}} (n : ℕ) (f : X ⟶ Y) (g : Y ⟶ Z) :
    restrict n (f ≫ g) = (restrict n f).comp (restrict n g) := by
  unfold restrict
  simp only [op_comp, Functor.map_comp, ModuleCat.hom_comp]

private theorem restrict_zero_of_factorization {X Y Z T : TopCat.{0}}
    (n : ℕ) (i : X ⟶ Y) (j : Y ⟶ T) (p : X ⟶ Z) (q : Z ⟶ T)
    (h : i ≫ j = p ≫ q) (hZ : IsZero (Betti n Z)) :
    (restrict n i).comp (restrict n j) = 0 := by
  rw [← restrict_comp, h, restrict_comp]
  have hz : (betti n).map q.op = 0 := hZ.eq_of_tgt _ _
  simp [restrict, hz]

open CycleQ2ProtectedComplexChart

/-- The composite restriction from projective five-space to the affine chart
of the protected sextic vanishes in every positive cohomological degree. -/
theorem ambient_to_chart_eq_zero {n : ℕ} (hn : n ≠ 0) :
    (restrict n chartInclusion).comp (restrict n projectiveInclusion) = 0 :=
  restrict_zero_of_factorization n chartInclusion projectiveInclusion affineInclusion
    affineChart chart_factorization (isZero_of_contractible _ _ AffineSpace n hn).unop

/-- Every degree-four Betti class on the protected projective sextic coming
from projective space restricts to zero on its chart with initial coordinate one. -/
theorem chart_degreeFour_eq_zero_of_ambient
    (c : Betti 4 ProjectiveHypersurface) (hc : c ∈ (restrict 4 projectiveInclusion).range) :
    restrict 4 chartInclusion c = 0 := by
  obtain ⟨a, rfl⟩ := hc
  exact DFunLike.congr_fun (ambient_to_chart_eq_zero (n := 4) (by decide)) a

open CycleQ2ProtectedComplexPrincipalOpen
open CycleQ2GeometricRegularDeRham (OpenRing TopDeRham residueClass)

/-- Restriction to the analytic points of the same localized ring used by the
protected regular de Rham complex. -/
def principalRestriction (s : OpenRing) (n : ℕ) :
    Betti n ProjectiveHypersurface →ₗ[ℂ] Betti n (TopCat.of (PrincipalPoints s)) :=
  restrict n (principalInclusion s ≫ chartInclusion)

/-- Ambient classes disappear on every protected principal open. -/
theorem ambient_to_principal_eq_zero (s : OpenRing) {n : ℕ} (hn : n ≠ 0) :
    (principalRestriction s n).comp (restrict n projectiveInclusion) = 0 := by
  rw [principalRestriction, restrict_comp, LinearMap.comp_assoc, ambient_to_chart_eq_zero hn,
    LinearMap.comp_zero]

/-- The support argument specialized to the actual analytic points of the protected
fourfold and of the smooth principal open. The comparison and the correspondence
are explicit hypotheses. The ambient contribution vanishes by the chart theorem. -/
theorem exact_of_principal_leray
    (s : OpenRing) (hs : s ≠ 0)
    (comparison : TopDeRham s →ₗ[ℂ] Betti 4 (TopCat.of (PrincipalPoints s)))
    (hinjective : Function.Injective comparison)
    (edge : Betti 4 ProjectiveHypersurface →ₗ[ℂ] ℂ)
    (a : Betti 4 ProjectiveSpace) (hedge : edge (restrict 4 projectiveInclusion a) = 1)
    (invariants : Submodule ℂ (Betti 4 ProjectiveHypersurface))
    (ha : restrict 4 projectiveInclusion a ∈ invariants)
    (projector : Module.End ℂ (Betti 4 ProjectiveHypersurface))
    (hgraded : ∀ x ∈ invariants ⊓ LinearMap.ker edge, projector x = x)
    (hsupport : (principalRestriction s 4).comp projector = 0)
    (x : Betti 4 ProjectiveHypersurface) (hx : x ∈ invariants)
    (hcomparison : comparison (residueClass s) = principalRestriction s 4 x) :
    ∃ η : CycleQ2AffineExterior.Form 3, CycleQ2AffineExterior.exteriorD3 η =
      CycleQ2AffineExactness.residueSourceForm CycleQ2AffineClearing.affineA := by
  exact CycleQ2GeometricExistence.exact_of_regular_open_leray s hs comparison hinjective
    edge _ hedge invariants ⊥ ha rfl _ projector
    (fun y hy => congrArg _ (hgraded y hy)) hsupport
    (DFunLike.congr_fun (ambient_to_principal_eq_zero s (n := 4) (by decide)) a)
    x hx hcomparison

end CycleQ2ProtectedHyperplaneSupport

#print axioms CycleQ2ProtectedHyperplaneSupport.ambient_to_chart_eq_zero
#print axioms CycleQ2ProtectedHyperplaneSupport.chart_degreeFour_eq_zero_of_ambient
#print axioms CycleQ2ProtectedHyperplaneSupport.ambient_to_principal_eq_zero
#print axioms CycleQ2ProtectedHyperplaneSupport.exact_of_principal_leray
