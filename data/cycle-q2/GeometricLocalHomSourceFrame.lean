import Proposal.GeometricLocalHomFrame

/-!
# Evaluating local homomorphisms in a source frame

A local generator of the source identifies its internal Hom into any module
sheaf with that target. The inverse sends a target section to the unique
homomorphism taking the generator to that section. A change of generator
acts on evaluation by its literal scalar on the target.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
noncomputable section

namespace CycleQ2LocalHomSourceFrame

open CategoryTheory Opposite AlgebraicGeometry TopologicalSpace
  CycleQ2GeometricIntrinsicNormal CycleQ2GeometricModuleLocalIso CycleQ2GeometricDifferentialSheaf

attribute [local instance] CycleQ2GeometricIntrinsicNormal.overHomCommModuleMk
  CycleQ2GeometricIntrinsicNormal.localLinearRingModule CycleQ2GeometricIntrinsicNormal.moduleHomObjModule

variable {X : Scheme.{0}} {M : X.Modules} (N : X.Modules) {U : X.Opens}
  (e : PatchIso (SheafOfModules.unit (ringSheaf X.sheaf)) M U)

local instance (L : X.Modules) (O : X.Opens) : Module Γ(X,O) (L.val.obj (op O)) :=
  (L.val.obj (op O)).isModule

local instance (O : X.Opens) : Module Γ(X,O) (LocalLinearHom X.sheaf M N O) :=
  localLinearHomModule X.sheaf M N O

private theorem generator_restrict {O P : X.Opens} (k : P ≤ O) (h : O ≤ U) :
    (M.val.map (homOfLE k).op (e.app O h (1 : Γ(X,O))) : M.val.obj (op P)) =
      e.app P (k.trans h) (1 : Γ(X,P)) := by
  have he := e.naturality k h (1 : Γ(X,O))
  change _ = e.app P _ (X.presheaf.map (homOfLE k).op (1 : Γ(X,O))) at he
  have h1 : X.presheaf.map (homOfLE k).op (1 : Γ(X,O)) = (1 : Γ(X,P)) :=
    map_one (X.presheaf.map (homOfLE k).op).hom
  exact he.trans (congrArg (e.app P (k.trans h)) h1)

private def extend (O : X.Opens) (h : O ≤ U) (y : N.val.obj (op O)) :
    LocalLinearHom X.sheaf M N O :=
  ⟨{
    app V := AddCommGrpCat.ofHom
      { toFun := fun x => (show Γ(X,V.unop.left) from (e.app V.unop.left (V.unop.hom.le.trans h)).symm x) •
          N.val.map V.unop.hom.op y
        map_zero' := by rw [map_zero, zero_smul]
        map_add' := by intro x x'; rw [map_add, add_smul] }
    naturality {V W} a := by
      apply ConcreteCategory.hom_ext
      intro x
      change (show Γ(X,W.unop.left) from (e.app W.unop.left (W.unop.hom.le.trans h)).symm
        (M.val.map a.unop.left.op x)) • N.val.map W.unop.hom.op y =
        N.val.map a.unop.left.op ((show Γ(X,V.unop.left) from
          (e.app V.unop.left (V.unop.hom.le.trans h)).symm x) • N.val.map V.unop.hom.op y)
      rw [N.val.map_smul, ← PresheafOfModules.map_comp_apply, ← op_comp, Over.w a.unop]
      exact congrArg (fun q : Γ(X,W.unop.left) => q • N.val.map W.unop.hom.op y)
        (e.symm.naturality a.unop.left.le (V.unop.hom.le.trans h) x).symm
  }, by
    intro V r x
    change (show Γ(X,V.left) from (e.app V.left (V.hom.le.trans h)).symm (r • x)) •
      N.val.map V.hom.op y = (show Γ(X,V.left) from r) • ((show Γ(X,V.left) from
        (e.app V.left (V.hom.le.trans h)).symm x) • N.val.map V.hom.op y)
    rw [map_smul, smul_eq_mul, mul_smul]⟩

private theorem extend_apply (O : X.Opens) (h : O ≤ U) (y : N.val.obj (op O))
    (V : Over O) (m : M.val.obj (op V.left)) :
    ((extend N e O h y).val.app (op V) m : N.val.obj (op V.left)) =
      (show Γ(X,V.left) from (e.app V.left (V.hom.le.trans h)).symm m) •
        (N.val.map V.hom.op y : N.val.obj (op V.left)) := rfl

private def value (O : X.Opens) (h : O ≤ U) :
    LocalLinearHom X.sheaf M N O →ₗ[Γ(X,O)] N.val.obj (op O) where
  toFun H := localLinearHomEvaluate X.sheaf M N O H (e.app O h (1 : Γ(X,O)))
  map_add' _ _ := rfl
  map_smul' r H := by
    have hr : X.presheaf.map (𝟙 O).op r = r := ConcreteCategory.congr_hom (X.presheaf.map_id (op O)) r
    exact congrArg (fun a : Γ(X,O) => a • localLinearHomEvaluate X.sheaf M N O H (e.app O h (1 : Γ(X,O)))) hr

private theorem on_basis (O : X.Opens) (h : O ≤ U) (H : LocalLinearHom X.sheaf M N O)
    (V : Over O) (r : Γ(X,V.left)) :
    H.val.app (op V) (e.app V.left (V.hom.le.trans h) r) =
      r • N.val.map V.hom.op (value N e O h H) := by
  have hs : e.app V.left (V.hom.le.trans h) r = r • e.app V.left (V.hom.le.trans h) (1 : Γ(X,V.left)) := by
    rw [← (e.app V.left (V.hom.le.trans h)).map_smul]
    exact congrArg (e.app V.left (V.hom.le.trans h)) (mul_one r).symm
  have hn := ConcreteCategory.congr_hom (H.val.naturality
    (Over.homMk V.hom : V ⟶ Over.mk (𝟙 O)).op) (e.app O h (1 : Γ(X,O)))
  change H.val.app (op V) (M.val.map V.hom.op (e.app O h (1 : Γ(X,O)))) =
    N.val.map V.hom.op (value N e O h H) at hn
  have hb : (H.val.app (op V) (e.app V.left (V.hom.le.trans h) (1 : Γ(X,V.left))) : N.val.obj (op V.left)) =
      N.val.map V.hom.op (value N e O h H) :=
    (congrArg (fun m : M.val.obj (op V.left) => (H.val.app (op V) m : N.val.obj (op V.left)))
      (generator_restrict e V.hom.le h).symm).trans hn
  let sm : N.val.obj (op V.left) → N.val.obj (op V.left) := fun z => r • z
  let m := e.app V.left (V.hom.le.trans h) (1 : Γ(X,V.left))
  have hlin : (H.val.app (op V) (r • m) : N.val.obj (op V.left)) = sm (H.val.app (op V) m) :=
    H.property V r m
  exact (congrArg (fun n : M.val.obj (op V.left) => (H.val.app (op V) n : N.val.obj (op V.left))) hs).trans
    (hlin.trans (congrArg sm hb))

private theorem value_bijective (O : X.Opens) (h : O ≤ U) : Function.Bijective (value N e O h) := by
  constructor
  · intro H K he
    apply localLinearHom_ext X.sheaf M N
    intro V x
    obtain ⟨r,rfl⟩ := (e.app V.left (V.hom.le.trans h)).surjective x
    exact (on_basis N e O h H V r).trans ((congrArg (fun z : N.val.obj (op O) =>
      (show Γ(X,V.left) from r) • N.val.map V.hom.op z) he).trans (on_basis N e O h K V r).symm)
  · intro y
    refine ⟨extend N e O h y, ?_⟩
    have h1 : (show Γ(X,O) from (e.app O h).symm (e.app O h (1 : Γ(X,O)))) = 1 :=
      (e.app O h).symm_apply_apply _
    have hy : (N.val.map (𝟙 O).op y : N.val.obj (op O)) = y :=
      ConcreteCategory.congr_hom (N.val.presheaf.map_id (op O)) y
    exact (extend_apply N e O h y (Over.mk (𝟙 O)) (e.app O h (1 : Γ(X,O)))).trans
      ((congrArg₂ (fun (a : Γ(X,O)) (m : N.val.obj (op O)) => a • m) h1 hy).trans (one_smul _ y))

/-- Evaluate every restricted local homomorphism on the chosen source generator. -/
def frame : PatchIso (moduleHomSheaf X.sheaf M N) N U where
  app O h := LinearEquiv.ofBijective (value N e O h) (value_bijective N e O h)
  naturality {O P} k h H := by
    change N.val.map (homOfLE k).op (localLinearHomEvaluate X.sheaf M N O H (e.app O h (1 : Γ(X,O)))) =
      localLinearHomEvaluate X.sheaf M N P
        (restrictLocalLinearHom X.sheaf M N (homOfLE k).op H) (e.app P (k.trans h) (1 : Γ(X,P)))
    exact (localLinearHomEvaluate_restrict X.sheaf M N (homOfLE k) H _).symm.trans
      (congrArg (localLinearHomEvaluate X.sheaf M N P (restrictLocalLinearHom X.sheaf M N (homOfLE k).op H))
        (generator_restrict e k h))

theorem frame_apply (O : X.Opens) (h : O ≤ U) (H : LocalLinearHom X.sheaf M N O) :
    (frame N e).app O h H = localLinearHomEvaluate X.sheaf M N O H (e.app O h (1 : Γ(X,O))) := rfl

/-- Scaling the actual source generator scales the evaluation in its target module. -/
theorem frame_change {V O : X.Opens} (e' : PatchIso (SheafOfModules.unit (ringSheaf X.sheaf)) M V)
    (h : O ≤ U) (h' : O ≤ V) (u : Γ(X,O))
    (he : e'.app O h' (1 : Γ(X,O)) = u • e.app O h (1 : Γ(X,O))) (H : LocalLinearHom X.sheaf M N O) :
    (frame N e').app O h' H = u • (frame N e).app O h H := by
  rw [frame_apply, frame_apply, he, map_smul]

end CycleQ2LocalHomSourceFrame
end

#print axioms CycleQ2LocalHomSourceFrame.frame
#print axioms CycleQ2LocalHomSourceFrame.frame_change
