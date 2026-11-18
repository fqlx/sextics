import Proposal.GeometricHodgeTwistTorusChart
import Proposal.GeometricHodgeTwistPolynomial
import Proposal.GeometricHodgeTwistNumerators
import Proposal.GeometricHodgeThreefoldCoordinateRegular

/-!
# Global sections and the original weighted cone

Every global section of O(n), for n nonnegative, is induced by a
homogeneous polynomial in the original five variables. Its pole-free
Laurent expansion gives the explicit numerator. A regular weight-one
coordinate gives uniqueness in the original cone quotient.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeTwistConeSections
open AlgebraicGeometry CategoryTheory
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeThreefoldTwist
open CycleQ2HodgeTwistAnchor CycleQ2HodgeTwistMonomials
open CycleQ2HodgeTwistTorusChart (globalSections)
open CycleQ2HodgeTwistPolynomial (representative representative_homogeneous representative_evaluation)
open CycleQ2GeometricSheafLocalIso (res res_self)
open CycleQ2GeometricModuleLocalIso (addSheaf)
open CycleQ2GenericSexticGradient (CoeffRing)

variable {R : Type} [CommRing R] [Nontrivial R] (φ : CoeffRing →+* R)
variable (h : IsUnit (φ vertexCoefficient)) (n : ℕ)

private abbrev H := Γ(twist φ (n : ℤ),⊤)
private abbrev F := addSheaf (twist φ (n : ℤ))

def torusFrame : H φ n →+ Γ(threefold φ,torus φ) :=
  (chartFrame φ n 0 (torus φ) (torus_le φ 0)).toAddMonoidHom.comp (res (F φ n) le_top)

include h in
theorem torusFrame_injective : Function.Injective (torusFrame φ n) := by
  intro a b he
  apply (globalSections φ h n).injective
  apply Subtype.ext
  have hsub := (chartFrame φ n 0 (torus φ) (torus_le φ 0)).injective he
  change (CycleQ2HodgeTwistCubicFaces.twistCoordinates φ 0 h Finset.univ (Finset.mem_univ 0) n
    (res (F φ n) le_top a)).val = _
  exact congrArg (fun w => (CycleQ2HodgeTwistCubicFaces.twistCoordinates φ 0 h
    Finset.univ (Finset.mem_univ 0) n w).val) hsub

theorem torusFrame_expansion (s : H φ n) : torusFrame φ n s =
    evaluate φ (torus φ) (torus_le φ) (commonCoefficient φ) 0 ((globalSections φ h n s).val) := by
  have he := face_frame_evaluation φ 0 h Finset.univ (Finset.mem_univ 0) (n : ℤ) (res (F φ n) le_top s)
  change chartFrame φ n 0 (torus φ) (torus_le φ 0) (res (F φ n) le_rfl (res (F φ n) le_top s)) = _ at he
  rw [res_self] at he
  exact he

private theorem torusFrame_homogeneous (a : grade φ n) :
    torusFrame φ n (homogeneousSection φ a.val a.property ⊤) =
      CycleQ2HodgeTwistNumerators.normalizedMap φ 0 n (torus φ) (torus_le φ 0) a := by
  change chartFrame φ n 0 (torus φ) (torus_le φ 0)
    (CycleQ2SeedSectionSheafLocal.moduleRes _ le_top (homogeneousSection φ a.val a.property ⊤)) = _
  rw [homogeneousSection_restrict, homogeneousSection_coordinate]
  rfl

include h in
def sectionMap : grade φ n →+ H φ n where
  toFun a := homogeneousSection φ a.val a.property ⊤
  map_zero' := by
    apply torusFrame_injective φ h n
    rw [torusFrame_homogeneous, map_zero, map_zero]
  map_add' a b := by
    apply torusFrame_injective φ h n
    rw [map_add, torusFrame_homogeneous, torusFrame_homogeneous, torusFrame_homogeneous, map_add]

theorem sectionMap_surjective : Function.Surjective (sectionMap φ h n) := by
  intro s
  let p := globalSections φ h n s
  let f := representative p
  let a : grade φ n := ⟨quotient φ f, quotient_mem_grade φ f (representative_homogeneous p)⟩
  refine ⟨a, ?_⟩
  apply torusFrame_injective φ h n
  change torusFrame φ n (homogeneousSection φ a.val a.property ⊤) = torusFrame φ n s
  rw [torusFrame_homogeneous, torusFrame_expansion φ h n s]
  exact representative_evaluation φ 0 p

theorem sectionMap_injective (hr : IsRegular (coord φ (0 : Fin 4).castSucc)) :
    Function.Injective (sectionMap φ h n) := by
  intro a b hab
  apply CycleQ2HodgeTwistNumerators.normalizedMap_injective φ 0 n hr
  let W := coordinateOpen φ 0
  let g (s : H φ n) := chartFrame φ n 0 W le_rfl (CycleQ2SeedSectionSheafLocal.moduleRes _ le_top s)
  have hg (x : grade φ n) : g (sectionMap φ h n x) = CycleQ2HodgeTwistNumerators.normalizedMap φ 0 n W le_rfl x := by
    change chartFrame φ n 0 W le_rfl
      (CycleQ2SeedSectionSheafLocal.moduleRes _ le_top (homogeneousSection φ x.val x.property ⊤)) = _
    rw [homogeneousSection_restrict, homogeneousSection_coordinate]
    rfl
  exact (hg a).symm.trans ((congrArg g hab).trans (hg b))

/-- The forward map sends each cone numerator to its original homogeneous Proj section. -/
def coneEquiv (hr : IsRegular (coord φ (0 : Fin 4).castSucc)) :
    grade φ n ≃+ Γ(twist φ (n : ℤ),⊤) :=
  AddEquiv.ofBijective (sectionMap φ h n) ⟨sectionMap_injective φ h n hr, sectionMap_surjective φ h n⟩

/-- On every domain fiber or domain coefficient base in the original monic locus, the
degree-n piece of the original cone is exactly the global sections of the n-th twist. -/
def gradedConeEquiv [IsDomain R] : grade φ n ≃+ Γ(twist φ (n : ℤ),⊤) :=
  coneEquiv φ h n (coord_isRegular φ h 0)

@[simp] theorem gradedConeEquiv_apply [IsDomain R] (a : grade φ n) :
    gradedConeEquiv φ h n a = homogeneousSection φ a.val a.property ⊤ := rfl

end CycleQ2HodgeTwistConeSections
end

#print axioms CycleQ2HodgeTwistConeSections.sectionMap_surjective
#print axioms CycleQ2HodgeTwistConeSections.coneEquiv

#print axioms CycleQ2HodgeTwistConeSections.gradedConeEquiv
