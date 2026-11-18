import Proposal.GeometricFiniteCechHOne
import Proposal.GeometricLiteralGlobalFunctions
import Proposal.GeometricSeedSectionSheafIso
import Proposal.GeometricSeedSectionNonempty

/-!
# Global functions on the moving divisor from its three chart primitives

Affine surjectivity of the closed immersion supplies local lifts. Their
pairwise differences lie in the actual ideal sheaf. A primitive for those
differences corrects the lifts to a compatible family of surface functions.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section

namespace CycleQ2LiteralMovingGlobalFunctions

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
  CycleQ2InjectiveCech CycleQ2GeometricSheafLocalIso CycleQ2FiniteInjectiveCech
  CycleQ2FiniteCechDescent CycleQ2GeometricModuleLocalIso CycleQ2GeometricIntrinsicNormal
  CycleQ2SeedProjectiveImageCocycle CycleQ2SeedSectionSheafKernel
  CycleQ2SeedSectionSheafCurveBinding CycleQ2ProjectiveCoordinateCohomology
open CycleQ2CechTwoToDerived (app app_res)

private theorem global_surjective_of_primitives {X : TopCat.{0}}
    {F G H : AbSheaf X} (a : F ⟶ G) (b : G ⟶ H) (U : Fin 3 → Opens X)
    (hcover : (⨆ i, U i) = ⊤)
    (hinj : ∀ W, Function.Injective (app a W))
    (hzero : ∀ W x, app b W (app a W x) = 0)
    (hker : ∀ W x, app b W x = 0 → ∃ y, app a W y = x)
    (hsurj : ∀ i, Function.Surjective (app b (U i)))
    (hprim : ∀ c : One F U, IsOneCocycle F U c → ∃ p : Zero F U, ∀ i j, i < j →
      res F (inf_le_right : U i ⊓ U j ≤ U j) (p j) - res F inf_le_left (p i) = c i j) :
    Function.Surjective (app b ⊤) := by
  intro s
  choose x hx using fun i => hsurj i (res H le_top s)
  have hdiff (i j : Fin 3) : app b (U i ⊓ U j)
      (res G inf_le_right (x j) - res G inf_le_left (x i)) = 0 := by
    rw [map_sub, app_res, app_res, hx, hx, res_comp, res_comp, sub_self]
  choose c hc using fun i j => hker (U i ⊓ U j) _ (hdiff i j)
  have hedge (i j : Fin 3) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
      app a W (res F (le_inf hi hj) (c i j)) = res G hj (x j) - res G hi (x i) := by
    rw [app_res, hc, map_sub, res_comp, res_comp]
  have hclosed : IsOneCocycle F U c := by
    intro i j k W hi hj hk
    apply hinj W
    rw [map_add, hedge i k W hi hk, hedge i j W hi hj, hedge j k W hj hk]
    abel
  obtain ⟨p,hp⟩ := hprim c hclosed
  let y : Zero G U := fun i => x i - app a (U i) (p i)
  have hinc (i j : Fin 3) (hij : i < j) (W : Opens X) (hi : W ≤ U i) (hj : W ≤ U j) :
      res G hi (y i) = res G hj (y j) := by
    have e := congrArg (res F (le_inf hi hj)) (hp i j hij)
    simp only [map_sub, res_comp] at e
    have he := congrArg (app a W) e
    rw [map_sub, hedge i j W hi hj, app_res, app_res] at he
    dsimp only [y]
    rw [map_sub, map_sub]
    linear_combination (norm := abel) he
  obtain ⟨r,hr⟩ := globalZero_exists U hcover y (by
    intro i j W hi hj
    rcases lt_trichotomy i j with h | rfl | h
    · exact hinc i j h W hi hj
    · rfl
    · exact (hinc j i h W hj hi).symm)
  refine ⟨r, globalZero_injective U hcover ?_⟩
  funext i
  change res H le_top (app b ⊤ r) = res H le_top s
  rw [← app_res]
  have e := congrFun hr i
  change res G le_top r = x i - app a (U i) (p i) at e
  rw [e, map_sub, hzero, sub_zero, hx]

abbrev vertex (i : Fin 3) := coordinateIntersection 57 1 {i}

abbrev IdealPrimitive (t : Fin 3 → ℂ) : Prop :=
  ∀ c : One (addSheaf (curveIdeal t)) vertex, IsOneCocycle (addSheaf (curveIdeal t)) vertex c →
    ∃ p : Zero (addSheaf (curveIdeal t)) vertex, ∀ i j, i < j →
      res _ (inf_le_right : vertex i ⊓ vertex j ≤ vertex j) (p j) - res _ inf_le_left (p i) = c i j

theorem moving_global_surjective (t : Fin 3 → ℂ) (h : IdealPrimitive t) :
    Function.Surjective (curveToSurface t).appTop := by
  let j := curveToSurface t
  let A := SheafOfModules.toSheaf Surface.ringCatSheaf
  let a := A.map (kernel.ι (schemeStructureMap j))
  let b := A.map (schemeStructureMap j)
  apply global_surjective_of_primitives a b vertex _ _ _ _ _ h
  · simpa only [vertex, coordinateIntersection_singleton] using coordinate_cover 57 1 one_ne_zero
  · intro W x y hxy
    apply (kernelIdealSectionEquiv j W).injective
    apply Subtype.ext
    change (kernel.ι (schemeStructureMap j)).val.app (op W) x =
      (kernel.ι (schemeStructureMap j)).val.app (op W) y at hxy
    rwa [kernelIdealSectionEquiv_coe, kernelIdealSectionEquiv_coe]
  · intro W x
    change j.app W ((kernel.ι (schemeStructureMap j)).val.app (op W) x) = 0
    rw [← kernelIdealSectionEquiv_coe]
    exact (kernelIdealSectionEquiv j W x).property
  · intro W r hr
    refine ⟨(kernelIdealSectionEquiv j W).symm ⟨r,hr⟩, ?_⟩
    change (kernel.ι (schemeStructureMap j)).val.app (op W) _ = r
    rw [← kernelIdealSectionEquiv_coe, LinearEquiv.apply_symm_apply]
  · intro i
    exact j.app_surjective _ (Proj.isAffineOpen_basicOpen _ _ (coordinateProduct_mem_grade 57 1 {i})
      (Finset.card_pos.mpr (Finset.singleton_nonempty i)))

abbrev Curve (t : Fin 3 → ℂ) :=
  CycleQ2SpecializedProjectiveCurve.specializedCurve CycleQ2SeedSectionCurveRows.seed t

/-- The coefficient map to the global ring of the moving curve is an isomorphism. -/
def movingGlobalFunctionsEquiv (t : Fin 3 → ℂ) (h : IdealPrimitive t) : ℂ ≃+* Γ(Curve t, ⊤) := by
  letI : Nonempty (Curve t) := CycleQ2SeedSectionNonempty.seed_specializedCurve_nonempty t
  letI : Nonempty (⊤ : (Curve t).Opens) := ⟨⟨Classical.ofNonempty, trivial⟩⟩
  let f := (curveToSurface t).appTop.hom.comp CycleQ2LiteralGlobalFunctions.globalFunctionsEquiv.toRingHom
  exact RingEquiv.ofBijective f ⟨f.injective, (moving_global_surjective t h).comp
    CycleQ2LiteralGlobalFunctions.globalFunctionsEquiv.surjective⟩

private theorem preconnected_of_domain (X : Scheme.{0}) [IsDomain Γ(X, ⊤)] : PreconnectedSpace X := by
  apply preconnectedSpace_iff_clopen.mpr
  intro s hs
  by_contra hn
  obtain ⟨hzero,hall⟩ := not_or.mp hn
  let U : X.Opens := ⟨s,hs.isOpen⟩
  let V : X.Opens := ⟨sᶜ,hs.isClosed.isOpen_compl⟩
  obtain ⟨x,hx⟩ := Set.nonempty_iff_ne_empty.mpr hzero
  obtain ⟨y,hy⟩ := Set.nonempty_compl.mpr hall
  let : Nonempty U := ⟨⟨x,hx⟩⟩
  let : Nonempty V := ⟨⟨y,hy⟩⟩
  have hdis : U ⊓ V = ⊥ := SetLike.ext' (Set.inter_compl_self s)
  have hcov : U ⊔ V = ⊤ := SetLike.ext' (Set.union_compl_self s)
  let e : Γ(X, U ⊔ V) ≅ CommRingCat.of (Γ(X,U) × Γ(X,V)) :=
    (X.sheaf.isProductOfDisjoint U V hdis).conePointUniqueUpToIso (CommRingCat.prodFanIsLimit _ _)
  let : IsDomain Γ(X, U ⊔ V) := hcov.symm ▸ inferInstanceAs (IsDomain Γ(X,⊤))
  let : IsDomain (Γ(X,U) × Γ(X,V)) := e.symm.commRingCatIsoToRingEquiv.toMulEquiv.isDomain _
  exact false_of_nontrivial_of_product_domain Γ(X,U) Γ(X,V)

theorem moving_connected (t : Fin 3 → ℂ) (h : IdealPrimitive t) : ConnectedSpace (Curve t) := by
  let : IsDomain Γ(Curve t, ⊤) := (movingGlobalFunctionsEquiv t h).symm.toMulEquiv.isDomain _
  exact { toPreconnectedSpace := preconnected_of_domain (Curve t),
          toNonempty := CycleQ2SeedSectionNonempty.seed_specializedCurve_nonempty t }

end CycleQ2LiteralMovingGlobalFunctions

end

#print axioms CycleQ2LiteralMovingGlobalFunctions.moving_global_surjective
#print axioms CycleQ2LiteralMovingGlobalFunctions.moving_connected
