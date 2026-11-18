import Proposal.GeometricLiteralResidueSheaf

/-!
# The coordinate one-forms on all opens of the Jacobian chart

The four global coordinate differentials of the affine ring give a basis
on every open of its spectrum. The decomposition of the identity into the
four coordinate projections already holds as an equality of sheaf maps.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false
set_option maxHeartbeats 700000

noncomputable section
namespace CycleQ2LiteralResidueOneFrame

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open CycleQ2GeometricRegularDeRham CycleQ2LiteralResidueSheaf CycleQ2GeometricAffineDerivations
open scoped KaehlerDifferential

abbrev OneModule : ModuleCat (CommRingCat.of OpenRing) := ModuleCat.of OpenRing Ω[OpenRing⁄ℂ]
private abbrev Rsec (U : Jacobian.Opens) := AffineSections (A := OpenRing) U
abbrev OneSheaf := tilde (R := CommRingCat.of OpenRing) OneModule

private abbrev B := CycleQ2GeometricAffineScheme.coordinateBasis

private def π₀ (i : Fin 4) : OneModule ⟶ ModuleCat.of OpenRing OpenRing :=
  ModuleCat.ofHom (B.coord i)

private def ι₀ (i : Fin 4) : ModuleCat.of OpenRing OpenRing ⟶ OneModule :=
  ModuleCat.ofHom (LinearMap.toSpanSingleton OpenRing _ (B i))

private def π (i : Fin 4) : OneSheaf ⟶ structureModule :=
  tilde.map (R := CommRingCat.of OpenRing) (π₀ i) ≫ (tildeSelf (R := CommRingCat.of OpenRing)).hom

private def ι (i : Fin 4) : structureModule ⟶ OneSheaf :=
  (tildeSelf (R := CommRingCat.of OpenRing)).inv ≫ tilde.map (R := CommRingCat.of OpenRing) (ι₀ i)

private theorem split : (∑ i : Fin 4, π i ≫ ι i) = 𝟙 OneSheaf := by
  have h : (∑ i : Fin 4, π₀ i ≫ ι₀ i) = 𝟙 OneModule := by
    apply ConcreteCategory.hom_ext
    intro w
    rw [Fin.sum_univ_four]
    change (B.repr w 0 • B 0 + B.repr w 1 • B 1 + B.repr w 2 • B 2 + B.repr w 3 • B 3) = w
    simpa only [Fin.sum_univ_four] using B.sum_repr w
  let F (f : OneModule ⟶ OneModule) : OneSheaf ⟶ OneSheaf :=
    tilde.map (R := CommRingCat.of OpenRing) f
  have hadd (f g : OneModule ⟶ OneModule) : F (f + g) = F f + F g :=
    tilde.map_add (R := CommRingCat.of OpenRing) f g
  have hid : F (𝟙 OneModule) = 𝟙 OneSheaf :=
    tilde.map_id (R := CommRingCat.of OpenRing)
  have hc (i : Fin 4) : F (π₀ i ≫ ι₀ i) = π i ≫ ι i := by
    simp only [π, ι, Category.assoc, Iso.hom_inv_id_assoc]
    exact tilde.map_comp (R := CommRingCat.of OpenRing) (π₀ i) (ι₀ i)
  have hh := congrArg F h
  rw [Fin.sum_univ_four] at hh ⊢
  rw [hadd, hadd, hadd, hc 0, hc 1, hc 2, hc 3, hid] at hh
  exact hh

def basisSection (U : Jacobian.Opens) (i : Fin 4) : OneSheaf.val.obj (op U) :=
  tilde.toOpen OneModule U (B i)

private theorem pi_basisSection (U : Jacobian.Opens) (i j : Fin 4) :
    (π i).val.app (op U) (basisSection U j) =
      (if j = i then 1 else 0 : Γ(Jacobian, U)) := by
  have h := ConcreteCategory.congr_hom (C := ModuleCat (CommRingCat.of OpenRing))
    (tilde.toOpen_map_app (R := CommRingCat.of OpenRing) (π₀ i) U) (B j)
  change _ = algebraMap OpenRing (Rsec U) (B.coord i (B j)) at h
  apply h.trans
  rw [Module.Basis.coord_apply, Module.Basis.repr_self, Finsupp.single_apply]
  split <;> simp_all only [map_one, map_zero]

private theorem iota_one (U : Jacobian.Opens) (i : Fin 4) :
    (ι i).val.app (op U) (1 : Γ(Jacobian, U)) = basisSection U i := by
  have h := ConcreteCategory.congr_hom (C := ModuleCat (CommRingCat.of OpenRing))
    (tilde.toOpen_map_app (R := CommRingCat.of OpenRing) (ι₀ i) U) 1
  change (ι i).val.app (op U) (algebraMap OpenRing (Rsec U) 1) =
    tilde.toOpen OneModule U ((1 : OpenRing) • B i) at h
  change (ι i).val.app (op U) (1 : Rsec U) = tilde.toOpen OneModule U (B i)
  simpa only [map_one, one_smul] using h

private theorem iota_apply (U : Jacobian.Opens) (i : Fin 4) (a : Γ(Jacobian, U)) :
    (ι i).val.app (op U) a = a • basisSection U i := by
  have h := ((ι i).val.app (op U)).hom.map_smul a (1 : Γ(Jacobian, U))
  change (ι i).val.app (op U) (show Γ(Jacobian, U) from a * 1) = a • (ι i).val.app (op U) (1 : Γ(Jacobian, U)) at h
  simpa only [mul_one, iota_one] using h

private def coordinates (U : Jacobian.Opens) :
    OneSheaf.val.obj (op U) ≃ₗ[Γ(Jacobian, U)] (Fin 4 → Γ(Jacobian, U)) where
  toFun w i := (π i).val.app (op U) w
  invFun a := ∑ i, a i • basisSection U i
  left_inv w := by
    have h := congrArg (fun f : OneSheaf ⟶ OneSheaf => f.val.app (op U) w) split
    change (∑ i : Fin 4, ((π i).val.app (op U) w : Γ(Jacobian, U)) • basisSection U i) = w
    rw [Fin.sum_univ_four] at h ⊢
    let c (i : Fin 4) : Γ(Jacobian, U) := (π i).val.app (op U) w
    change (ι 0).val.app (op U) (c 0) + (ι 1).val.app (op U) (c 1) +
      (ι 2).val.app (op U) (c 2) + (ι 3).val.app (op U) (c 3) = w at h
    rw [iota_apply U 0, iota_apply U 1, iota_apply U 2, iota_apply U 3] at h
    exact h
  right_inv a := by
    funext i
    change ((π i).val.app (op U)).hom (∑ j, a j • basisSection U j) = a i
    simp only [map_sum, map_smul]
    change (∑ j : Fin 4, (a j : Γ(Jacobian, U)) * (show Γ(Jacobian, U) from (π i).val.app (op U) (basisSection U j))) = _
    simp [pi_basisSection, mul_ite]
  map_add' x y := by funext i; exact map_add ((π i).val.app (op U)).hom x y
  map_smul' a x := by funext i; exact map_smul ((π i).val.app (op U)).hom a x

/-- The basis of all sections of the sheaf associated to the Kähler module. -/
def sectionBasis (U : Jacobian.Opens) :
    Module.Basis (Fin 4) Γ(Jacobian, U) (OneSheaf.val.obj (op U)) :=
  Module.Basis.ofEquivFun (coordinates U)

theorem sectionBasis_apply (U : Jacobian.Opens) (i : Fin 4) :
    sectionBasis U i = basisSection U i := by
  have h := congrFun (Module.Basis.coe_ofEquivFun (coordinates U)) i
  change sectionBasis U i = (coordinates U).symm (Pi.single i 1) at h
  rw [h]
  apply (coordinates U).injective
  rw [LinearEquiv.apply_symm_apply]
  funext j
  change (Pi.single i (1 : Γ(Jacobian, U)) : Fin 4 → Γ(Jacobian, U)) j = (show Γ(Jacobian, U) from (π j).val.app (op U) (basisSection U i))
  rw [pi_basisSection, Pi.single_apply]
  simp [eq_comm]

theorem sectionBasis_restrict {U V : Jacobian.Opens} (h : V ⟶ U) (i : Fin 4) :
    OneSheaf.val.map h.op (sectionBasis U i) = sectionBasis V i := by
  rw [sectionBasis_apply, sectionBasis_apply]
  rfl

end CycleQ2LiteralResidueOneFrame
end

#print axioms CycleQ2LiteralResidueOneFrame.sectionBasis_restrict
