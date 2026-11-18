import Proposal.GeometricHodgeEulerContractionSheaf

/-!
# Evaluation of the tangent sheaf on every subopen of a free cotangent chart

On a Kähler basis chart, restriction of the dual coordinate functionals
gives a frame of the intrinsic tangent sheaf. Evaluation at any subopen is
an equivalence with the ordinary linear dual of the differential sections.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option maxHeartbeats 700000
set_option maxRecDepth 3000
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section
namespace CycleQ2HodgeVolumeContraction

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry Module
open CycleQ2GeometricDifferentialSheaf CycleQ2GeometricIntrinsicNormal
  CycleQ2GeometricDifferentialRestriction CycleQ2GeometricAffineChartSections
  CycleQ2GeometricDifferentialChartTransport CycleQ2GeometricFunctionalDifferentials CycleQ2GeometricSheafKaehlerMap
  CycleQ2LiteralThreefoldDifferentialFrame CycleQ2HodgeEulerContractionSheaf

variable {X : Scheme.{0}} (M : SheafOfModules.{0} (ringSheaf X.sheaf))

def evaluation (W : X.Opens) :
    (dual M).val.obj (op W) →ₗ[Γ(X,W)] (M.val.obj (op W) →ₗ[Γ(X,W)] Γ(X,W)) where
  toFun := localLinearHomEvaluate X.sheaf M _ W
  map_add' x y := LinearMap.ext fun _ => rfl
  map_smul' r v := by
    apply LinearMap.ext
    intro m
    change X.presheaf.map (𝟙 W).op r * _ = r * _
    simp
    rfl

variable {U : X.Opens} {A : Type} [CommRing A] [Algebra ℂ A]
  (e : U.toScheme ≅ Spec (CommRingCat.of A)) (f : X ⟶ Spec (CommRingCat.of ℂ))
  (h : e.inv ≫ U.ι ≫ f = Spec.map (CommRingCat.ofHom (algebraMap ℂ A)))
  {n : ℕ} (b : Basis (Fin n) A (KaehlerDifferential ℂ A))

abbrev oneForms := differentialSheaf X.sheaf (schemeCoefficient f)

theorem basis_restrict {V W : Over U} (a : V ⟶ W) (i : Fin n) :
    (oneForms f).val.map a.left.op (sectionBasis e f h b W i) = sectionBasis e f h b V i := by
  rw [sectionBasis_apply, sectionBasis_apply]
  exact sectionLift_restriction X.sheaf (schemeCoefficient f) _ _ W.left (chartSection e W)
    (chartSection_complex e f h W) V.left a.left.le (chartSection e V)
    (chartSection_complex e f h V) (chartSection_naturality e a) (b i)

def dualCoordinate (j : Fin n) : (dual (oneForms f)).val.obj (op U) :=
  (localLinearHomEquiv X.sheaf (oneForms f) _ U).symm (chartCoefficientMap e f h (b.coord j))

private theorem coord_apply (W : Over U) (j k : Fin n) :
    evaluation (oneForms f) W.left ((dual (oneForms f)).val.map W.hom.op (dualCoordinate e f h b j))
        (sectionBasis e f h b W k) = (if k = j then 1 else 0) := by
  change (sectionEquiv e f h b W (sectionBasis e f h b W k)) j = _
  change (sectionBasis e f h b W).equivFun (sectionBasis e f h b W k) j = _
  simp

include h b in
private theorem eval_injective (W : Over U) :
    Function.Injective (evaluation (oneForms f) W.left) := by
  intro v w hv
  apply Subtype.ext
  apply NatTrans.ext
  funext V
  apply ConcreteCategory.hom_ext
  intro x
  let L : Over W.left := V.unop
  let T : Over U := Over.mk (L.hom ≫ W.hom)
  have he : evaluateOn (oneForms f) W.left v L = evaluateOn (oneForms f) W.left w L := by
    apply (sectionBasis e f h b T).ext
    intro j
    let a : T ⟶ W := Over.homMk L.hom
    rw [← basis_restrict e f h b a]
    have p := ConcreteCategory.congr_hom (v.val.naturality
      (Over.homMk L.hom : L ⟶ Over.mk (𝟙 W.left)).op) (sectionBasis e f h b W j)
    have q := ConcreteCategory.congr_hom (w.val.naturality
      (Over.homMk L.hom : L ⟶ Over.mk (𝟙 W.left)).op) (sectionBasis e f h b W j)
    exact p.trans ((congrArg ((X.presheaf.map L.hom.op))
      (LinearMap.congr_fun hv (sectionBasis e f h b W j))).trans q.symm)
  exact LinearMap.congr_fun he x

def evaluationEquiv (W : Over U) : (dual (oneForms f)).val.obj (op W.left) ≃ₗ[Γ(X,W.left)]
    ((oneForms f).val.obj (op W.left) →ₗ[Γ(X,W.left)] Γ(X,W.left)) := by
  apply LinearEquiv.ofBijective (evaluation (oneForms f) W.left)
  refine ⟨eval_injective e f h b W, ?_⟩
  intro v
  refine ⟨∑ j, v (sectionBasis e f h b W j) •
    (dual (oneForms f)).val.map W.hom.op (dualCoordinate e f h b j), ?_⟩
  apply (sectionBasis e f h b W).ext
  intro k
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  calc
    _ = ∑ j, v (sectionBasis e f h b W j) * (if k = j then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro j _
      exact congrArg (v (sectionBasis e f h b W j) * ·) (coord_apply e f h b W j k)
    _ = _ := by simp [mul_ite] <;> rfl

end CycleQ2HodgeVolumeContraction
end

#print axioms CycleQ2HodgeVolumeContraction.evaluationEquiv
