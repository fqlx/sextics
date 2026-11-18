import Proposal.GeometricHodgeEulerTangentSheaf
import Proposal.GeometricHodgeEulerSheafCoefficients
import Proposal.GeometricHodgeEulerOverlap

/-!
# Affine sections and homogeneous coordinates of the weighted hypersurface

On every subopen of the i-th weight-one chart the affine coordinate map
sends a dehomogenized polynomial to its homogeneous fraction. This
identifies the entries of the Euler and gradient maps in the two charts.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeEulerTangentCoordinates

open AlgebraicGeometry CategoryTheory MvPolynomial
open CycleQ2GenericSexticGradient (CoeffRing)
open CycleQ2GeometricIncidenceProj (geometricWeight)
open CycleQ2GeometricHodgeThreefold CycleQ2HodgeEuler CycleQ2HodgeEulerChartBinding
open CycleQ2HodgeEulerSheaf
open CycleQ2HodgeTwistRatios (normalized)
open CycleQ2GeometricAffineChartSections
open CycleQ2HodgeEulerTangentSheaf (functions functions_apply)

variable {R : Type} [CommRing R] (φ : CoeffRing →+* R) (i : Fin 4)

private theorem native_functions :
    (Scheme.ΓSpecIso (CommRingCat.of (ChartRing φ i))).inv ≫ (coordinateChart φ i).hom.appTop ≫
      (coordinateOpen φ i).topIso.hom = Proj.awayToSection (grade φ) (coord φ i.castSucc) := by
  change _ ≫ (Proj.basicOpenToSpec (grade φ) (coord φ i.castSucc)).app ⊤ ≫
    (Proj.basicOpen (grade φ) (coord φ i.castSucc)).topIso.hom = _
  rw [Proj.basicOpenToSpec_app_top]
  simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id, Iso.inv_hom_id_assoc]

private theorem functions_relabel {Y : Scheme.{0}} {U : Y.Opens} {A B : Type}
    [CommRing A] [CommRing B] (e : U.toScheme ≅ Spec (CommRingCat.of A))
    (b : A ≃+* B) (a : B) :
    functions (X := Y) (U := U) (A := B) (e ≪≫ Scheme.Spec.mapIso b.toCommRingCatIso.symm.op) a =
      functions e (b.symm a) := by
  let g : CommRingCat.of B ⟶ CommRingCat.of A := CommRingCat.ofHom b.symm.toRingHom
  have h : (Scheme.ΓSpecIso (CommRingCat.of B)).inv ≫ (e.hom ≫ Spec.map g).appTop ≫ U.topIso.hom =
      g ≫ (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ e.hom.appTop ≫ U.topIso.hom := by
    simp only [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_inv_naturality_assoc]
  exact ConcreteCategory.congr_hom h a

private theorem functions_of_map {Y : Scheme.{0}} {U : Y.Opens} {A : Type} [CommRing A]
    (e : U.toScheme ≅ Spec (CommRingCat.of A)) (g : CommRingCat.of A ⟶ Γ(Y,U))
    (h : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ e.hom.appTop ≫ U.topIso.hom = g) (a : A) :
    functions e a = g.hom a := ConcreteCategory.congr_hom h a

private theorem functions_relabel_of_map {Y : Scheme.{0}} {U : Y.Opens} {K A B : Type}
    [CommRing K] [CommRing A] [CommRing B] [Algebra K A] [Algebra K B] (e : U.toScheme ≅ Spec (CommRingCat.of A))
    (g : CommRingCat.of A ⟶ Γ(Y,U))
    (h : (Scheme.ΓSpecIso (CommRingCat.of A)).inv ≫ e.hom.appTop ≫ U.topIso.hom = g)
    (b : A ≃ₐ[K] B) (a : B) :
    functions (X := Y) (U := U) (A := B) (e ≪≫ Scheme.Spec.mapIso b.toRingEquiv.toCommRingCatIso.symm.op) a =
      g.hom (b.symm a) :=
  (functions_relabel e b.toRingEquiv a).trans (functions_of_map e g h (b.symm a))

theorem functions_affineChart (a : chart φ i) :
    functions (X := threefold φ) (U := coordinateOpen φ i) (A := chart φ i) (affineChart φ i) a =
      (Proj.awayToSection (grade φ) (coord φ i.castSucc)).hom ((chartEquiv φ i).symm a) :=
  functions_relabel_of_map (K := R) (Y := threefold φ) (U := coordinateOpen φ i) (A := ChartRing φ i)
    (B := chart φ i) (coordinateChart φ i) (Proj.awayToSection (grade φ) (coord φ i.castSucc))
    (native_functions φ i) (chartEquiv φ i) a

variable (V : (threefold φ).Opens) (hi : V ≤ coordinateOpen φ i)

/-- The actual affine chart section of every element of the quotient ring,
on every subopen, is restriction of its homogeneous degree-zero fraction. -/
theorem chartSection_eq_sectionMap (a : chart φ i) :
    chartSection (affineChart φ i) (Over.mk (homOfLE hi)) a =
      sectionMap φ i V hi ((chartEquiv φ i).symm a) := by
  have hr := chartSection_naturality (affineChart φ i)
    (Over.homMk (homOfLE hi) : Over.mk (homOfLE hi) ⟶ Over.mk (𝟙 (coordinateOpen φ i))) a
  exact hr.symm.trans (congrArg ((threefold φ).presheaf.map (homOfLE hi).op)
    ((functions_apply (affineChart φ i) a).symm.trans (functions_affineChart φ i a)))

theorem chartSection_normalized {n : ℕ} (p : MvPolynomial (Fin 5) R)
    (hp : p.IsWeightedHomogeneous geometricWeight n) :
    chartSection (affineChart φ i) (Over.mk (homOfLE hi)) (chartMap φ i (dehom i p)) =
      normalized φ i (quotient φ p) (quotient_mem_grade φ p hp) V hi := by
  change _ = sectionMap φ i V hi (fraction φ i n p hp)
  rw [chartSection_eq_sectionMap, ← chartEquiv_fraction φ i n p hp, AlgEquiv.symm_apply_apply]

theorem chartSection_coordinate (j : Fin 5) :
    chartSection (affineChart φ i) (Over.mk (homOfLE hi)) (coordinate φ i j) =
      normalized φ i (coord φ j) (coord_mem_grade φ j) V hi :=
  chartSection_normalized φ i V hi (X j) (isWeightedHomogeneous_X _ _ _)

theorem chartSection_partial (j : Fin 5) :
    chartSection (affineChart φ i) (Over.mk (homOfLE hi)) (conePartial φ i j) =
      normalized φ i (partialValue φ j) (partial_mem φ j) V hi := by
  rw [chartSection_eq_sectionMap, ← chartEquiv_gradientRatio φ i j, AlgEquiv.symm_apply_apply,
    sectionMap_gradient]

section LocalEvaluation

open Opposite CycleQ2GeometricDifferentialSheaf CycleQ2GeometricChartTangentMaps
open CycleQ2HodgeEulerTangentSheaf

variable {X : Scheme.{0}} {U W : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]

/-- On each subopen the restricted intrinsic tangent section differentiates
the image of every affine coordinate-ring element. -/
theorem evaluate_restrict_tangentSection (e : U.toScheme ≅ Spec (CommRingCat.of A))
    (f : X ⟶ Spec (CommRingCat.of ℂ))
    (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
    (hW : W ≤ U) (D : Derivation ℂ A A) (a : A) :
    evaluate f ((tangent f).val.map (homOfLE hW).op (tangentSection e f h D))
        ((universalDifferential X.sheaf (schemeCoefficient f)).d (X := op W)
          (chartSection e (Over.mk (homOfLE hW)) a)) =
      chartSection e (Over.mk (homOfLE hW)) (D a) := by
  let g := homOfLE hW
  let s := tangentSection e f h D
  have he := presheafHom_map_app_op_mk_id (F := (cotangent f).val.presheaf)
    (G := (functionsModule X).val.presheaf) g s.val
  exact (ConcreteCategory.congr_hom he _).trans ((chartLinearMap_D e f h D (Over.mk g) _).trans
    (chartDerivation_section e f h D (Over.mk g) a))

/-- The five normalized coordinate differentials recover the Euler quotient
after restriction to every subopen of a weight-one chart. -/
theorem evaluate_restrict_normalized (ψ : CoeffRing →+* ℂ) (l : Fin 4)
    (W : (threefold ψ).Opens) (hW : W ≤ coordinateOpen ψ l) (v : RawTangent ψ l) (j : Fin 5) :
    evaluate (toBase ψ) ((tangent (toBase ψ)).val.map (homOfLE hW).op
        (quotientTangentSections ψ l (Submodule.Quotient.mk v)))
      ((universalDifferential (threefold ψ).sheaf (schemeCoefficient (toBase ψ))).d (X := op W)
        (normalized ψ l (coord ψ j) (coord_mem_grade ψ j) W hW)) =
      chartSection (affineChart ψ l) (Over.mk (homOfLE hW))
        (v.val j - v.val l.castSucc * radial ψ l j) := by
  rw [← chartSection_coordinate ψ l W hW j]
  exact (evaluate_restrict_tangentSection (affineChart ψ l) (toBase ψ) (affineChart_overBase ψ l) hW
    (tangentQuotientEquiv ψ l (Submodule.Quotient.mk v)) (coordinate ψ l j)).trans
    (congrArg (chartSection (affineChart ψ l) (Over.mk (homOfLE hW)))
      (tangentQuotientEquiv_coordinate_all ψ l v j))

end LocalEvaluation

end CycleQ2HodgeEulerTangentCoordinates
end

#print axioms CycleQ2HodgeEulerTangentCoordinates.chartSection_eq_sectionMap
#print axioms CycleQ2HodgeEulerTangentCoordinates.chartSection_partial

#print axioms CycleQ2HodgeEulerTangentCoordinates.evaluate_restrict_normalized
