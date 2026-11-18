import Proposal.ScratchCechDeRhamTotalThree

/-! Projection from degree-three total cohomology to ordinary degree-three
cohomology of the chosen vertex, with the explicit cycle condition included. -/

set_option autoImplicit false
set_option Elab.async false
noncomputable section
namespace CycleQ2CechDeRhamTotalThree

universe u v
variable (B : Double.{u}) (V₂ V₃ V₄ : AddCommGrpCat.{v})
    (d₂ : V₂ →+ V₃) (d₃ : V₃ →+ V₄) (dsq : ∀ x, d₃ (d₂ x) = 0)

def localBounds : V₂ →+ d₃.ker := d₂.codRestrict d₃.ker dsq

abbrev LocalCohomology := d₃.ker ⧸ (localBounds V₂ V₃ V₄ d₂ d₃ dsq).range

variable (e₂ : B.X 0 2 →+ V₂) (e₃ : B.X 0 3 →+ V₃) (e₄ : B.X 0 4 →+ V₄)
    (comm₂ : ∀ x, d₂ (e₂ x) = e₃ (B.v 0 2 x))
    (comm₃ : ∀ x, d₃ (e₃ x) = e₄ (B.v 0 3 x))

def vertexCycle : Cycles B →+ d₃.ker where
  toFun z := ⟨e₃ z.1.1, by
    change d₃ (e₃ z.1.1) = 0
    have hz : B.v 0 3 z.1.1 = 0 := congrArg Prod.fst z.2
    rw [comm₃,hz,map_zero]⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ _ _)

/-- The ordinary cohomology class of the bidegree (0,3) component evaluated
on the selected open. The hypotheses are the two naturality squares for
restriction of two- and three-forms. -/
def vertexCohomologyMap : HThree B →+ LocalCohomology V₂ V₃ V₄ d₂ d₃ dsq :=
  let q := QuotientAddGroup.mk' (localBounds V₂ V₃ V₄ d₂ d₃ dsq).range
  QuotientAddGroup.lift _ (q.comp (vertexCycle B V₃ V₄ d₃ e₃ e₄ comm₃)) (by
    rintro z ⟨x,rfl⟩
    apply (QuotientAddGroup.eq_zero_iff _).mpr
    exact ⟨e₂ x.1,Subtype.ext (comm₂ x.1)⟩)

@[simp] theorem vertexCohomologyMap_classOf (z : Cycles B) :
    vertexCohomologyMap B V₂ V₃ V₄ d₂ d₃ dsq e₂ e₃ e₄ comm₂ comm₃ (classOf B z) =
      QuotientAddGroup.mk (vertexCycle B V₃ V₄ d₃ e₃ e₄ comm₃ z) := rfl

end CycleQ2CechDeRhamTotalThree
end

#print axioms CycleQ2CechDeRhamTotalThree.vertexCohomologyMap
