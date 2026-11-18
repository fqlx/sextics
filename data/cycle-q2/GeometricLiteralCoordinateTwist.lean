import Proposal.GeometricSeedSectionSheafLocal
import Proposal.GeometricSeedSectionSheafGlobal

/-!
# Coordinate twists on the three original seed patches

The degree k twist is the kernel gluing the patch structure modules by
x_i = (X_i/X_j)^(-k) x_j. Every subopen of a patch has its canonical
coordinate frame, with the original transition under a change of patch.

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

attribute [local instance] CycleQ2SeedSectionSheafSections.patchSectionsCommRing

def scalarUnit (k : ℤ) (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) : Γ(Surface,V)ˣ :=
  transitionUnit i j V hi hj ^ (-k)

theorem scalarUnit_restrict (k : ℤ) (i j : Fin 3) (V W : Surface.Opens)
    (hWV : W ≤ V) (hi : V ≤ Patch i) (hj : V ≤ Patch j) :
    Units.map (targetRes hWV).toMonoidHom (scalarUnit k i j V hi hj) =
      scalarUnit k i j W (hWV.trans hi) (hWV.trans hj) := by
  unfold scalarUnit
  rw [map_zpow]
  exact congrArg (fun x : Γ(Surface,W)ˣ => x ^ (-k)) (transitionUnit_restrict i j V W hWV hi hj)

theorem scalarUnit_cocycle (k : ℤ) (i j l : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) (hl : V ≤ Patch l) :
    scalarUnit k i j V hi hj * scalarUnit k j l V hj hl = scalarUnit k i l V hi hl := by
  rw [scalarUnit, scalarUnit, scalarUnit, ← mul_zpow, mul_comm, transitionUnit_cocycle]

abbrev patchModule (i : Fin 3) : Surface.Modules := patchStructure (Patch i)

def overlapScalar (k : ℤ) (i j : Fin 3) :
    patchStructure (PairPatch i j) ⟶ patchStructure (PairPatch i j) :=
  patchScalar (PairPatch i j) (scalarUnit k i j _ inf_le_left inf_le_right)

set_option backward.isDefEq.respectTransparency true in
set_option backward.isDefEq.respectTransparency.types true in
theorem overlapScalar_negFour (i j : Fin 3) : overlapScalar (-4) i j = pairTwist i j := by
  let U := PairPatch i j
  let u := transitionUnit i j U inf_le_left inf_le_right
  have h : ((u ^ (-(-4 : ℤ)) : Γ(Surface,U)ˣ) : Γ(Surface,U)) = (u : Γ(Surface,U)) ^ 4 := by
    simp
  exact congrArg (patchScalar U) h

theorem overlapScalar_coordinate (k : ℤ) (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) (y : Γ(patchStructure (PairPatch i j), V)) :
    patchSectionsEquiv (PairPatch i j) V (le_inf hi hj) ((overlapScalar k i j).app V y) =
      (scalarUnit k i j V hi hj : Γ(Surface,V)) *
        patchSectionsEquiv (PairPatch i j) V (le_inf hi hj) y := by
  rw [overlapScalar, patchSectionsEquiv_scalar]
  exact congrArg (fun u : Γ(Surface,V)ˣ => (u : Γ(Surface,V)) * _)
    (scalarUnit_restrict k i j (PairPatch i j) V (le_inf hi hj) inf_le_left inf_le_right)

abbrev overlapTarget : Surface.Modules :=
  ∏ᶜ (fun p : Fin 3 × Fin 3 => patchStructure (PairPatch p.1 p.2))

private def onPatch (j : Fin 3) (V : Surface.Opens) : Γ(patchModule j,V) ≃+ Γ(patchModule j,V ⊓ Patch j) :=
  pushforwardInfEquiv (X := Surface) (Patch j) (structureModule _) V

private theorem onPatch_apply (j : Fin 3) (V : Surface.Opens) (s : Γ(patchModule j,V)) :
    onPatch j V s = moduleRes (X := Surface) (patchModule j) inf_le_left s :=
  pushforwardInfEquiv_apply (X := Surface) (Patch j) (structureModule _) V s

private theorem onPatch_symm_restrict (j : Fin 3) (V W : Surface.Opens) (hWV : W ≤ V) (hj : W ≤ Patch j)
    (s : Γ(patchModule j,V ⊓ Patch j)) :
    moduleRes (X := Surface) (patchModule j) hWV ((onPatch j V).symm s) =
      moduleRes (X := Surface) (patchModule j) (le_inf hWV hj) s :=
  pushforwardInfEquiv_symm_restrict_subopen (X := Surface) (Patch j) (structureModule _) V W hWV hj s

def difference (k : ℤ) : (∏ᶜ patchModule) ⟶ overlapTarget :=
  Pi.lift fun p : Fin 3 × Fin 3 =>
    Pi.π patchModule p.1 ≫ patchStructureRestriction (show PairPatch p.1 p.2 ≤ _ from inf_le_left) -
      Pi.π patchModule p.2 ≫ patchStructureRestriction inf_le_right ≫ overlapScalar k p.1 p.2

abbrev ambientTwist (k : ℤ) : Surface.Modules := kernel (difference k)

def projection (k : ℤ) (i : Fin 3) : ambientTwist k ⟶ patchModule i :=
  kernel.ι (difference k) ≫ Pi.π patchModule i

theorem projection_compatible (k : ℤ) (i j : Fin 3) :
    projection k i ≫ patchStructureRestriction (show PairPatch i j ≤ _ from inf_le_left) =
      projection k j ≫ patchStructureRestriction inf_le_right ≫ overlapScalar k i j := by
  let L : patchModule i ⟶ patchStructure (PairPatch i j) := patchStructureRestriction inf_le_left
  let R : patchModule j ⟶ patchStructure (PairPatch i j) := patchStructureRestriction inf_le_right ≫ overlapScalar k i j
  let pr := Pi.π (fun p : Fin 3 × Fin 3 => patchStructure (PairPatch p.1 p.2)) (i,j)
  have hD : difference k ≫ pr = Pi.π patchModule i ≫ L - Pi.π patchModule j ≫ R :=
    Pi.lift_π _ _
  apply sub_eq_zero.mp
  calc
    _ = kernel.ι (difference k) ≫ (Pi.π patchModule i ≫ L) -
          kernel.ι (difference k) ≫ (Pi.π patchModule j ≫ R) :=
      congrArg₂ (· - ·) (Category.assoc (kernel.ι _) (Pi.π patchModule i) L)
        (Category.assoc (kernel.ι _) (Pi.π patchModule j) R)
    _ = kernel.ι (difference k) ≫ (difference k ≫ pr) := by rw [hD, Preadditive.comp_sub]
    _ = 0 := (Category.assoc (kernel.ι _) (difference k) pr).symm.trans
      ((congrArg (fun f : ambientTwist k ⟶ overlapTarget => f ≫ pr) (kernel.condition _)).trans
        Limits.zero_comp)

def coordinate (k : ℤ) (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    Γ(ambientTwist k,V) →ₗ[Γ(Surface,V)] Γ(Surface,V) := patchMap (projection k i) V hi

theorem coordinate_restrict (k : ℤ) (i : Fin 3) {V W : Surface.Opens}
    (hWV : W ≤ V) (hi : V ≤ Patch i) (x : Γ(ambientTwist k,V)) :
    targetRes hWV (coordinate k i V hi x) =
      coordinate k i W (hWV.trans hi) (moduleRes (X := Surface) (ambientTwist k) hWV x) :=
  patchMap_restrict _ hWV hi x

theorem coordinate_transition (k : ℤ) (i j : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (hj : V ≤ Patch j) (x : Γ(ambientTwist k,V)) :
    coordinate k i V hi x = (scalarUnit k i j V hi hj : Γ(Surface,V)) * coordinate k j V hj x := by
  have h := congrArg (fun f : ambientTwist k ⟶ patchStructure (PairPatch i j) =>
    patchSectionsEquiv (PairPatch i j) V (le_inf hi hj) (f.app V x)) (projection_compatible k i j)
  change patchSectionsEquiv (PairPatch i j) V (le_inf hi hj)
      ((patchStructureRestriction (show PairPatch i j ≤ Patch i from inf_le_left)).app V ((projection k i).app V x)) =
    patchSectionsEquiv (PairPatch i j) V (le_inf hi hj) ((overlapScalar k i j).app V
      ((patchStructureRestriction (show PairPatch i j ≤ Patch j from inf_le_right)).app V ((projection k j).app V x))) at h
  rw [patchSectionsEquiv_patchRestriction, overlapScalar_coordinate, patchSectionsEquiv_patchRestriction] at h
  exact h

/-- A section of the ambient twist is determined by its ordinary chart coordinates. -/
theorem section_ext (k : ℤ) (V : Surface.Opens) (x y : Γ(ambientTwist k,V))
    (h : ∀ j : Fin 3, coordinate k j (V ⊓ Patch j) inf_le_right
      (moduleRes (X := Surface) (ambientTwist k) inf_le_left x) =
      coordinate k j (V ⊓ Patch j) inf_le_right
        (moduleRes (X := Surface) (ambientTwist k) inf_le_left y)) : x = y := by
  apply (sectionKernelEquiv (difference k) V).injective
  apply Subtype.ext
  rw [sectionKernelEquiv_val, sectionKernelEquiv_val]
  apply (sectionProductEquiv patchModule V).injective
  funext j
  rw [sectionProductEquiv_apply, sectionProductEquiv_apply]
  change (projection k j).app V x = (projection k j).app V y
  apply (onPatch j V).injective
  rw [onPatch_apply, onPatch_apply]
  rw [moduleRes_app (X := Surface) (projection k j), moduleRes_app (X := Surface) (projection k j)]
  exact (patchSectionsEquiv (Patch j) (V ⊓ Patch j) inf_le_right).injective (h j)

theorem coordinate_injective (k : ℤ) (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    Function.Injective (coordinate k i V hi) := by
  intro x y h
  apply section_ext k V x y
  intro j
  have hVi : V ⊓ Patch j ≤ Patch i := inf_le_left.trans hi
  rw [coordinate_transition k j i _ inf_le_right hVi,
    coordinate_transition k j i _ inf_le_right hVi,
    ← coordinate_restrict k i inf_le_left hi x, ← coordinate_restrict k i inf_le_left hi y, h]

private def chartFamily (k : ℤ) (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
    (x : Γ(Surface,V)) (j : Fin 3) : Γ(patchModule j,V) :=
  (onPatch j V).symm
    ((patchSectionsEquiv (Patch j) (V ⊓ Patch j) inf_le_right).symm
      ((scalarUnit k j i (V ⊓ Patch j) inf_le_right (inf_le_left.trans hi) : Γ(Surface,_)) *
        targetRes inf_le_left x))

private theorem chartFamily_coordinate (k : ℤ) (i : Fin 3) (V W : Surface.Opens)
    (hWV : W ≤ V) (hi : V ≤ Patch i) (j : Fin 3) (hj : W ≤ Patch j) (x : Γ(Surface,V)) :
    patchSectionsEquiv (Patch j) W hj (moduleRes (X := Surface) (patchModule j) hWV (chartFamily k i V hi x j)) =
      (scalarUnit k j i W hj (hWV.trans hi) : Γ(Surface,W)) * targetRes hWV x := by
  unfold chartFamily
  rw [onPatch_symm_restrict j V W hWV hj]
  change patchSectionsEquiv (Patch j) W hj ((patchStructure _).presheaf.map (homOfLE (le_inf hWV hj)).op _) = _
  rw [patchSectionsEquiv_restrict (Patch j) (le_inf hWV hj) (show V ⊓ Patch j ≤ Patch j from inf_le_right),
    RingEquiv.apply_symm_apply, map_mul]
  have hu := congrArg (fun g : Γ(Surface,W)ˣ => (g : Γ(Surface,W)))
    (scalarUnit_restrict k j i (V ⊓ Patch j) W (le_inf hWV hj) inf_le_right (inf_le_left.trans hi))
  change targetRes (le_inf hWV hj) _ * targetRes (le_inf hWV hj) (targetRes inf_le_left x) = _
  rw [targetRes_comp]
  exact congrArg (fun a : Γ(Surface,W) => a * targetRes hWV x) hu

private def familyProduct (k : ℤ) (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
    (x : Γ(Surface,V)) : Γ(∏ᶜ patchModule,V) :=
  (sectionProductEquiv patchModule V).symm (chartFamily k i V hi x)

private theorem familyProduct_mem (k : ℤ) (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
    (x : Γ(Surface,V)) : familyProduct k i V hi x ∈ ((difference k).app V).hom.ker := by
  change (difference k).app V _ = 0
  apply (sectionProductEquiv (fun p : Fin 3 × Fin 3 => patchStructure (PairPatch p.1 p.2)) V).injective
  funext p
  rw [sectionProductEquiv_apply, map_zero]
  change (difference k ≫ Pi.π (fun p : Fin 3 × Fin 3 => patchStructure (PairPatch p.1 p.2)) p).app V _ = 0
  rw [difference, Pi.lift_π]
  rcases p with ⟨j,l⟩
  change (patchStructureRestriction (show PairPatch j l ≤ _ from inf_le_left)).app V
      ((Pi.π patchModule j).app V (familyProduct k i V hi x)) -
    (overlapScalar k j l).app V ((patchStructureRestriction inf_le_right).app V
      ((Pi.π patchModule l).app V (familyProduct k i V hi x))) = 0
  rw [familyProduct, sectionProductEquiv_symm_apply, sectionProductEquiv_symm_apply]
  apply sub_eq_zero.mpr
  let W : Surface.Opens := V ⊓ PairPatch j l
  have hWV : W ≤ V := inf_le_left
  have hWj : W ≤ Patch j := inf_le_right.trans inf_le_left
  have hWl : W ≤ Patch l := inf_le_right.trans inf_le_right
  apply (pairPatchInfEquiv j l V).injective
  rw [pairPatchInfEquiv_apply, pairPatchInfEquiv_apply]
  rw [moduleRes_app (X := Surface) (M := patchModule j) (N := patchStructure (PairPatch j l))
      (patchStructureRestriction (show PairPatch j l ≤ Patch j from inf_le_left)),
    moduleRes_app (X := Surface) (M := patchStructure (PairPatch j l)) (N := patchStructure (PairPatch j l))
      (overlapScalar k j l),
    moduleRes_app (X := Surface) (M := patchModule l) (N := patchStructure (PairPatch j l))
      (patchStructureRestriction (show PairPatch j l ≤ Patch l from inf_le_right))]
  apply (patchSectionsEquiv (PairPatch j l) W inf_le_right).injective
  rw [patchSectionsEquiv_patchRestriction (U := Patch j) (V := PairPatch j l) (W := W) inf_le_left inf_le_right,
    overlapScalar_coordinate k j l W hWj hWl,
    patchSectionsEquiv_patchRestriction (U := Patch l) (V := PairPatch j l) (W := W) inf_le_right inf_le_right]
  rw [chartFamily_coordinate k i V W hWV hi j hWj, chartFamily_coordinate k i V W hWV hi l hWl]
  rw [← mul_assoc, ← Units.val_mul, scalarUnit_cocycle]

private def coordinateSection (k : ℤ) (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i)
    (x : Γ(Surface,V)) : Γ(ambientTwist k,V) :=
  (sectionKernelEquiv (difference k) V).symm ⟨familyProduct k i V hi x, familyProduct_mem k i V hi x⟩

private theorem coordinateSection_spec (k : ℤ) (i : Fin 3) (V : Surface.Opens)
    (hi : V ≤ Patch i) (x : Γ(Surface,V)) :
    coordinate k i V hi (coordinateSection k i V hi x) = x := by
  change patchSectionsEquiv (Patch i) V hi ((Pi.π patchModule i).app V
    ((kernel.ι (difference k)).app V ((sectionKernelEquiv (difference k) V).symm _))) = x
  rw [sectionKernelEquiv_symm_val]
  change patchSectionsEquiv (Patch i) V hi ((Pi.π patchModule i).app V
    ((sectionProductEquiv patchModule V).symm (chartFamily k i V hi x))) = x
  rw [sectionProductEquiv_symm_apply]
  have H := chartFamily_coordinate k i V V (le_refl V) hi i hi x
  simp only [moduleRes_refl, scalarUnit, transitionUnit_self, one_zpow, Units.val_one, one_mul] at H
  exact H.trans (by change Surface.presheaf.map (𝟙 (op V)) x = x; simp)

/-- Trivialization of the genuine kernel sheaf over any subopen of a coordinate patch. -/
def coordinateEquiv (k : ℤ) (i : Fin 3) (V : Surface.Opens) (hi : V ≤ Patch i) :
    Γ(ambientTwist k,V) ≃ₗ[Γ(Surface,V)] Γ(Surface,V) :=
  LinearEquiv.ofBijective (coordinate k i V hi) ⟨coordinate_injective k i V hi,
    fun x => ⟨coordinateSection k i V hi x, coordinateSection_spec k i V hi x⟩⟩

end CycleQ2LiteralMovingIdealExact
end

#print axioms CycleQ2LiteralMovingIdealExact.coordinateEquiv
