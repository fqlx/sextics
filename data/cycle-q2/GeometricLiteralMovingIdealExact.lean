import Proposal.GeometricLiteralCoordinateTwist
import Proposal.GeometricSeedSectionSheafIso
import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# The twisted coordinate sheaf and the moving-curve ideal

On the three coordinate patches, sections of the degree k twist satisfy
x_i = (X_i/X_j)^(-k) x_j. In degree -4 the chart inclusions of the orbit
ideals therefore embed the original twisted ideal into this sheaf. The
regular moving section identifies its actual curve ideal with that submodule.

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

private def inclusionFamily : twistedIdeal ⟶ ∏ᶜ patchModule :=
  Pi.lift fun i => chartProjection i ≫ idealPatchInclusion i

private theorem inclusionFamily_difference : inclusionFamily ≫ difference (-4) = 0 := by
  apply Pi.hom_ext
  intro p
  rw [Category.assoc, difference, Pi.lift_π, Preadditive.comp_sub, Limits.zero_comp]
  apply sub_eq_zero.mpr
  simpa only [inclusionFamily, Pi.lift_π_assoc, overlapScalar_negFour, leftIdealToPair,
    rightIdealToPair, Category.assoc] using chartProjection_compatibility p.1 p.2

def orbitInclusion : twistedIdeal ⟶ ambientTwist (-4) :=
  kernel.lift _ inclusionFamily inclusionFamily_difference

@[reassoc] theorem orbitInclusion_projection (i : Fin 3) :
    orbitInclusion ≫ projection (-4) i = chartProjection i ≫ idealPatchInclusion i := by
  rw [projection, orbitInclusion, kernel.lift_ι_assoc, inclusionFamily, Pi.lift_π]

set_option maxHeartbeats 800000 in
theorem coordinate_orbitInclusion (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (x : Γ(twistedIdeal,V)) :
    coordinate (-4) i V hi (orbitInclusion.app V x) = sourceCoordinate i V hi x := by
  let E := patchSectionsEquiv (Patch i) V hi
  have h := congrArg (fun f : twistedIdeal ⟶ patchModule i => f.app V x) (orbitInclusion_projection i)
  exact congrArg E h

instance orbitInclusion_mono : Mono orbitInclusion where
  right_cancellation {M} f g h := by
    apply Scheme.Modules.hom_ext
    intro V
    apply ConcreteCategory.hom_ext
    intro z
    apply sourceFamily_injective V
    funext i
    apply idealPatchInclusion_app_injective i V
    let coord (m : M ⟶ ambientTwist (-4)) := (projection (-4) i).app V (m.app V z)
    have hproj (x : Γ(twistedIdeal,V)) :=
      congrArg (fun q : twistedIdeal ⟶ patchModule i => q.app V x) (orbitInclusion_projection i)
    exact (hproj (f.app V z)).symm.trans ((congrArg coord h).trans (hproj (g.app V z)))

/-- The sheaf quotient by the actual orbit-ideal inclusion, independent of the moving vector. -/
abbrev orbitQuotient := cokernel orbitInclusion

def movingIdealComplex (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) : ShortComplex Surface.Modules :=
  ShortComplex.mk ((twistedIdealCurveIso t ht).inv ≫ orbitInclusion) (cokernel.π orbitInclusion)
    (by rw [Category.assoc, cokernel.condition, Limits.comp_zero])

theorem movingIdeal_shortExact (t : Fin 3 → ℂ) (ht : ∀ i, ChartRegular t i) :
    (movingIdealComplex t ht).ShortExact := by
  let C := ShortComplex.mk orbitInclusion (cokernel.π _) (cokernel.condition _)
  have hC : C.ShortExact := {
    exact := ShortComplex.exact_cokernel orbitInclusion
    mono_f := orbitInclusion_mono
    epi_g := inferInstanceAs (Epi (cokernel.π orbitInclusion)) }
  let e : C ≅ movingIdealComplex t ht := ShortComplex.isoMk (twistedIdealCurveIso t ht)
    (Iso.refl _) (Iso.refl _) (by simp [C, movingIdealComplex]) (by simp [C, movingIdealComplex])
  exact ShortComplex.shortExact_of_iso e hC

end CycleQ2LiteralMovingIdealExact
end

#print axioms CycleQ2LiteralMovingIdealExact.coordinate_orbitInclusion
#print axioms CycleQ2LiteralMovingIdealExact.movingIdeal_shortExact
