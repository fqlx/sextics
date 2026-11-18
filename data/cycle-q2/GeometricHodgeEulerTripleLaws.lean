import Proposal.GeometricHodgeEulerTripleContraction

/-!
# Additive and restriction laws for the native triple contraction

The composite of the genuine contractions on each open has a scalar value.
All three tangent arguments are additive. Restricting that scalar agrees
with applying the same contractions to the restricted fields and form.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2HodgeEulerTripleLaws

open CategoryTheory Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2GeometricExteriorSheaf CycleQ2GeometricDifferentialSheaf
  CycleQ2GeometricIntrinsicNormal CycleQ2LocalSheafificationFrame
  CycleQ2GeometricExteriorLocalFrames CycleQ2HodgeEulerContractionSheaf
  CycleQ2LiteralAbelJacobiSurfaceWedge CycleQ2HodgeEulerTripleContraction
open CycleQ2LiteralThreefoldResidueContraction (interior interior_add)

variable {X : Scheme.{0}} (M : SheafOfModules.{0} (ringSheaf X.sheaf))
variable (U : X.Opens)

private abbrev O := SheafOfModules.unit (ringSheaf X.sheaf)
private abbrev raw := exteriorPresheaf X.sheaf.obj M.val 3
private abbrev present := toExteriorSheaf X.sheaf M.val 3
private abbrev presentation := @overPresentation (show TopCat from X)
  (ringSheaf X.sheaf) (raw M) U (form M 3) (present M)

local instance presentationInjective :
    PresheafOfModules.IsLocallyInjective ((Opens.grothendieckTopology X).over U)
      (presentation M U) :=
  @overPresentation_locallyInjective (show TopCat from X) (ringSheaf X.sheaf) (raw M) U (form M 3)
    (present M) (exteriorPresentation_locallyInjective X.sheaf M.val 3)

local instance presentationSurjective :
    PresheafOfModules.IsLocallySurjective ((Opens.grothendieckTopology X).over U)
      (presentation M U) :=
  @overPresentation_locallySurjective (show TopCat from X) (ringSheaf X.sheaf) (raw M) U (form M 3)
    (present M) (exteriorPresentation_locallySurjective X.sheaf M.val 3)

private def onOpen (s t u : Γ(dual M,U)) : (form M 3).over U ⟶ (O (X := X)).over U :=
  contractOver M U s ≫ twoToOneOver M U t ≫ (localLinearHomEquiv X.sheaf M (O (X := X)) U) u

private def sectionHom (s t u : Γ(dual M,U)) : LocalLinearHom X.sheaf (form M 3) (O (X := X)) U :=
  (localLinearHomEquiv X.sheaf (form M 3) (O (X := X)) U).symm (onOpen M U s t u)

private theorem onExterior (s t u : Γ(dual M,U)) (V : Over U) (x : ⋀[Γ(X,V.left)]^3 (M.val.obj (op V.left))) :
    (sectionHom M U s t u).val.app (op V) (exteriorSection X.sheaf M.val 3 V.left x) =
      evaluateOn M U u V (contract (evaluateOn M U t V) (interior 2 (evaluateOn M U s V) x)) := by
  change evaluateOn M U u V ((twoToOneOver M U t).val.app (op V)
    ((contractOver M U s).val.app (op V) (exteriorSection X.sheaf M.val 3 V.left x))) = _
  rw [contractOver_exterior, twoToOneOver_exterior]

private theorem hom_ext (g k : LocalLinearHom X.sheaf (form M 3) (O (X := X)) U)
    (he : ∀ (V : Over U) (x : ⋀[Γ(X,V.left)]^3 (M.val.obj (op V.left))),
      g.val.app (op V) (exteriorSection X.sheaf M.val 3 V.left x) =
        k.val.app (op V) (exteriorSection X.sheaf M.val 3 V.left x)) : g = k := by
  apply (localLinearHomEquiv X.sheaf (form M 3) (O (X := X)) U).injective
  apply SheafOfModules.hom_ext
  apply (PresheafOfModules.homEquivOfIsLocallyBijective
    (presentation M U) ((O (X := X)).over U).isSheaf).injective
  apply PresheafOfModules.hom_ext
  intro V
  apply ConcreteCategory.hom_ext
  exact he V.unop

private theorem sectionHom_restrict {V : X.Opens} (f : V ⟶ U) (s t u : Γ(dual M,U)) :
    restrictLocalLinearHom X.sheaf (form M 3) (O (X := X)) f.op (sectionHom M U s t u) =
      sectionHom M V ((dual M).val.map f.op s) ((dual M).val.map f.op t) ((dual M).val.map f.op u) := by
  apply hom_ext
  intro W x
  let W' : Over U := Over.mk (W.hom ≫ f)
  exact (onExterior M U s t u W' x).trans
    (onExterior M V ((dual M).val.map f.op s) ((dual M).val.map f.op t) ((dual M).val.map f.op u) W x).symm

theorem triple_restrict {V : X.Opens} (h : V ≤ U) (s t u : Γ(dual M,U)) (ω : Γ(form M 3,U)) :
    X.presheaf.map (homOfLE h).op (triple M U s t u ω) =
      triple M V ((dual M).val.map (homOfLE h).op s) ((dual M).val.map (homOfLE h).op t)
        ((dual M).val.map (homOfLE h).op u) ((form M 3).val.map (homOfLE h).op ω) := by
  have hn := localLinearHomEvaluate_restrict X.sheaf (form M 3) (O (X := X))
    (homOfLE h) (sectionHom M U s t u) ω
  rw [sectionHom_restrict] at hn
  exact hn.symm

private theorem evaluateOn_add (s t : Γ(dual M,U)) (V : Over U) :
    evaluateOn M U (s+t) V = evaluateOn M U s V + evaluateOn M U t V :=
  LinearMap.ext fun _ => rfl

private theorem contract_add {R N : Type} [CommRing R] [AddCommGroup N] [Module R N]
    (a b : N →ₗ[R] R) (x : ⋀[R]^2 N) : contract (a+b) x = contract a x + contract b x := by
  have hx : x ∈ Submodule.span R (Set.range (exteriorPower.ιMulti R 2)) := by
    rw [exteriorPower.ιMulti_span]
    trivial
  induction hx using Submodule.span_induction with
  | mem x hx =>
      obtain ⟨v, rfl⟩ := hx
      simp only [contract, exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
      change (a (v 0) + b (v 0)) • v 1 - (a (v 1) + b (v 1)) • v 0 = _
      simp only [add_smul]
      change _ = (a (v 0) • v 1 - a (v 1) • v 0) + (b (v 0) • v 1 - b (v 1) • v 0)
      abel
  | zero => simp only [map_zero, add_zero]
  | add x y _ _ hx hy => simp only [map_add, hx, hy]; abel
  | smul r y _ hy => simp only [map_smul, hy, smul_add]

private theorem apply_add (s t u s' t' u' s'' t'' u'' : Γ(dual M,U))
    (h : ∀ (V : Over U) (x : ⋀[Γ(X,V.left)]^3 (M.val.obj (op V.left))),
      evaluateOn M U u V (contract (evaluateOn M U t V) (interior 2 (evaluateOn M U s V) x)) =
      evaluateOn M U u' V (contract (evaluateOn M U t' V) (interior 2 (evaluateOn M U s' V) x)) +
      evaluateOn M U u'' V (contract (evaluateOn M U t'' V) (interior 2 (evaluateOn M U s'' V) x)))
    (ω : Γ(form M 3,U)) :
    triple M U s t u ω = triple M U s' t' u' ω + triple M U s'' t'' u'' ω := by
  have he : sectionHom M U s t u = sectionHom M U s' t' u' + sectionHom M U s'' t'' u'' := by
    apply hom_ext
    intro V x
    change _ = (sectionHom M U s' t' u').val.app (op V) _ + (sectionHom M U s'' t'' u'').val.app (op V) _
    rw [onExterior, onExterior, onExterior]
    exact h V x
  exact congrArg (fun d : LocalLinearHom X.sheaf (form M 3) (O (X := X)) U =>
    d.val.app (op (Over.mk (𝟙 U))) ω) he

theorem triple_add_left (s s' t u : Γ(dual M,U)) (ω : Γ(form M 3,U)) :
    triple M U (s+s') t u ω = triple M U s t u ω + triple M U s' t u ω := by
  apply apply_add
  intro V x
  simp only [evaluateOn_add, interior_add, LinearMap.add_apply, map_add]

theorem triple_add_middle (s t t' u : Γ(dual M,U)) (ω : Γ(form M 3,U)) :
    triple M U s (t+t') u ω = triple M U s t u ω + triple M U s t' u ω := by
  apply apply_add
  intro V x
  simp only [evaluateOn_add, contract_add, map_add]

theorem triple_add_right (s t u u' : Γ(dual M,U)) (ω : Γ(form M 3,U)) :
    triple M U s t (u+u') ω = triple M U s t u ω + triple M U s t u' ω := by
  apply apply_add
  intro V x
  rw [evaluateOn_add, LinearMap.add_apply]

def evaluation (ω : Γ(form M 3,U)) : Γ(dual M,U) →+ Γ(dual M,U) →+ Γ(dual M,U) →+ Γ(X,U) :=
  AddMonoidHom.mk' (fun s => AddMonoidHom.mk' (fun t => AddMonoidHom.mk'
    (fun u => triple M U s t u ω) (fun u w => triple_add_right M U s t u w ω))
    (fun t w => AddMonoidHom.ext fun u => triple_add_middle M U s t w u ω))
    (fun s w => AddMonoidHom.ext fun t => AddMonoidHom.ext fun u => triple_add_left M U s w t u ω)

end CycleQ2HodgeEulerTripleLaws
end

#print axioms CycleQ2HodgeEulerTripleLaws.triple_restrict
#print axioms CycleQ2HodgeEulerTripleLaws.evaluation
