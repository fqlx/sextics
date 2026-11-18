import Proposal.GeometricLiteralMovingIdealExact

/-!
# The twisted orbit quotient on the original affine patches

After restriction to a seed patch, the quotient by the actual orbit
inclusion is the tilde sheaf of the ring modulo its original orbit ideal.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency true
set_option backward.isDefEq.respectTransparency.types true

noncomputable section

namespace CycleQ2LiteralMovingIdealExact

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
  CycleQ2SeedProjectiveImageCocycle CycleQ2SeedProjectiveImageChart CycleQ2SeedSectionSheaf
  CycleQ2GeometricSurfaceDehomogenizedCharts
  CycleQ2SeedSectionSheafSections CycleQ2SeedSectionSheafTwist CycleQ2SeedSectionSheafLimits
  CycleQ2SeedSectionSheafMono CycleQ2SeedSectionSheafLocal CycleQ2SeedSectionSheafGlobal
  CycleQ2SeedSectionSheafKernel CycleQ2SeedSectionSheafIso CycleQ2SeedSectionAffineInjective

attribute [local instance] CycleQ2SeedSectionSheafSections.patchSectionsCommRing

def patchTrivialization (k : ℤ) (i : Fin 3) :
    (Scheme.Modules.restrictFunctor (Patch i).ι).obj (ambientTwist k) ⟶ structureModule (Patch i).toScheme :=
  (Scheme.Modules.restrictFunctor (Patch i).ι).map (projection k i) ≫
    (Scheme.Modules.restrictAdjunction (Patch i).ι).counit.app (structureModule _)

instance patchTrivialization_isIso (k : ℤ) (i : Fin 3) : IsIso (patchTrivialization k i) := by
  apply Scheme.Modules.Hom.isIso_iff_isIso_app.mpr
  intro U
  apply (ConcreteCategory.isIso_iff_bijective _).mpr
  let V := (Patch i).ι ''ᵁ U
  have hi : V ≤ Patch i := by
    simpa only [Scheme.Opens.opensRange_ι] using (Patch i).ι.image_le_opensRange U
  have hf : Function.Bijective ((projection k i).app V) :=
    ((patchSectionsEquiv (Patch i) V hi).bijective.of_comp_iff' _).mp (coordinateEquiv k i V hi).bijective
  exact (ConcreteCategory.bijective_of_isIso
    (((Scheme.Modules.restrictAdjunction (Patch i).ι).counit.app (structureModule _)).app U)).comp hf

private theorem adjoint_projection_square {C D : Type*} [Category C] [Category D]
    {L : C ⥤ D} {R : D ⥤ C} (A : L ⊣ R) {X Y : C} {P Q : D}
    (a : X ⟶ Y) (p : X ⟶ R.obj P) (q : Y ⟶ R.obj Q) (x : P ⟶ Q)
    (h : a ≫ q = p ≫ R.map x) :
    L.map a ≫ L.map q ≫ A.counit.app Q = (L.map p ≫ A.counit.app P) ≫ x := by
  rw [← L.map_comp_assoc, h, L.map_comp, Category.assoc, Category.assoc]
  exact congrArg (fun f => L.map p ≫ f) (A.counit.naturality x)

set_option maxHeartbeats 1200000 in
theorem patchInclusion_comm (i : Fin 3) :
    (Scheme.Modules.restrictFunctor (Patch i).ι).map orbitInclusion ≫ patchTrivialization (-4) i =
      (chartRestrictionIso i).hom ≫ chartInclusion i :=
  adjoint_projection_square (Scheme.Modules.restrictAdjunction (Patch i).ι)
    (X := twistedIdeal) (Y := ambientTwist (-4)) (P := chartIdeal i) (Q := structureModule (Patch i).toScheme)
    orbitInclusion (chartProjection i) (projection (-4) i) (chartInclusion i) (orbitInclusion_projection i)

/-- In each original affine chart the quotient is the structure module modulo
the literal orbit ideal inclusion. -/
def orbitQuotient_patch (i : Fin 3) :
    (Scheme.Modules.restrictFunctor (Patch i).ι).obj orbitQuotient ≅ cokernel (chartInclusion i) :=
  PreservesCokernel.iso _ orbitInclusion ≪≫
    cokernel.mapIso _ _ (chartRestrictionIso i) (asIso (patchTrivialization (-4) i)) (patchInclusion_comm i)

/-- The chart quotient is the tilde sheaf of the ordinary affine orbit quotient
ring, transported along the original coordinate chart isomorphism. -/
def orbitQuotient_affine (i : Fin 3) :
    (Scheme.Modules.restrictFunctor (Patch i).ι).obj orbitQuotient ≅
      (Scheme.Modules.restrictFunctor (coordinateAffineChart 57 1 i.succ).hom).obj
        (tilde (ModuleCat.of (AffineRing i) ((AffineRing i) ⧸ OrbitIdeal i))) := by
  let A := CommRingCat.of (AffineRing i)
  let R := Scheme.Modules.restrictFunctor (coordinateAffineChart 57 1 i.succ).hom
  let f := ModuleCat.ofHom (OrbitIdeal i).subtype
  let T := tilde.functor A
  letI : T.PreservesZeroMorphisms := ⟨fun _ _ => tilde.map_zero⟩
  letI : T.IsLeftAdjoint := (tilde.adjunction (R := A)).isLeftAdjoint
  let eS : T.obj (ModuleCat.of A A) ≅ structureModule (Spec A) := tildeSelf
  letI : IsIso eS.hom := eS.isIso_hom
  let e : cokernel f ≅ ModuleCat.of A (A ⧸ OrbitIdeal i) :=
    ModuleCat.cokernelIsoRangeQuotient f ≪≫ (Submodule.quotEquivOfEq _ _
      (show f.hom.range = OrbitIdeal i from Submodule.range_subtype _)).toModuleIso
  exact orbitQuotient_patch i ≪≫ cokernelCompIsIso (R.map (affineInclusion i)) _ ≪≫
    (PreservesCokernel.iso R (affineInclusion i)).symm ≪≫ R.mapIso
      (cokernelCompIsIso (T.map f) eS.hom ≪≫
        (PreservesCokernel.iso T f).symm ≪≫ T.mapIso e)

end CycleQ2LiteralMovingIdealExact
end

#print axioms CycleQ2LiteralMovingIdealExact.orbitQuotient_affine
