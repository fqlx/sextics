import Proposal.GeometricGenericSweptFunctionField
import Proposal.GeometricClosedSupportedRestriction
import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor

/-!
# The derived stalk of the generic swept correspondence

Every term of a complex pushed forward from the true generic swept scheme
has zero stalk at the geometric function point of the first affine chart.
The derived stalk thus annihilates the entire supported complex, including
morphisms that factor through it.

Prepared for fqlx with OpenAI ChatGPT assistance. See solution.md.
-/

set_option autoImplicit false
set_option Elab.async false
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.types false

noncomputable section
namespace CycleQ2GenericSweptDerivedStalk

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
  CycleQ2GenericSweptExtSupport CycleQ2GenericSweptFunctionField
open CycleQ2IncidenceEtaleParameter (parameterScheme)
open CycleQ2ClosedEmbeddingSheafExact (push)

attribute [local instance] HasDerivedCategory.standard

abbrev sheaves (S : Scheme.{0}) := (show TopCat from S).Sheaf AddCommGrpCat.{0}
abbrev stalkAt (x : Threefold) : sheaves Threefold ⥤ AddCommGrpCat.{0} :=
  TopCat.Sheaf.forget AddCommGrpCat (show TopCat from Threefold) ⋙
    TopCat.Presheaf.stalkFunctor AddCommGrpCat x

abbrev functionStalk := stalkAt (functionPoint (default : Spec (CommRingCat.of chartField)))

variable {V : parameterScheme.Opens} {t : Fin 3 → ℂ}

abbrev supportedComplex (C : CochainComplex (sheaves (swept V t)) ℤ) :=
  ((push (inclusion V t).base).mapHomologicalComplex (ComplexShape.up ℤ)).obj C

theorem supportedSheaf_stalk_zero {x : Threefold} (hx : x ∈ complement V t)
    (F : sheaves (swept V t)) :
    IsZero ((stalkAt x).obj ((push (inclusion V t).base).obj F)) := by
  apply AddCommGrpCat.isZero_iff_subsingleton.mpr
  exact CycleQ2ClosedSupportedRestriction.push_stalk_off_range (inclusion V t).base
    (inclusion V t).isClosedEmbedding F hx

theorem supportedComplex_stalk_zero {x : Threefold} (hx : x ∈ complement V t)
    (C : CochainComplex (sheaves (swept V t)) ℤ) :
    IsZero (((stalkAt x).mapHomologicalComplex (ComplexShape.up ℤ)).obj (supportedComplex C)) := by
  apply (IsZero.iff_id_eq_zero _).mpr
  apply HomologicalComplex.hom_ext
  intro n
  exact (supportedSheaf_stalk_zero hx (C.X n)).eq_of_src _ _

/-- Off the swept image, the entire supported complex has zero derived stalk. -/
theorem derivedStalk_off {x : Threefold} (hx : x ∈ complement V t)
    (C : CochainComplex (sheaves (swept V t)) ℤ) :
    IsZero ((stalkAt x).mapDerivedCategory.obj (DerivedCategory.Q.obj (supportedComplex C))) :=
  ((stalkAt x).mapDerivedCategoryFactors.app (supportedComplex C)).isZero_iff.mpr
    (DerivedCategory.Q.map_isZero (supportedComplex_stalk_zero hx C))

theorem derivedStalk_zero (hd : topologicalKrullDim (swept V t) ≤ 2)
    (C : CochainComplex (sheaves (swept V t)) ℤ) :
    IsZero (functionStalk.mapDerivedCategory.obj (DerivedCategory.Q.obj (supportedComplex C))) :=
  derivedStalk_off (functionPoint_mem_complement hd _) C

theorem derivedStalk_factor_zero (hd : topologicalKrullDim (swept V t) ≤ 2)
    (C : CochainComplex (sheaves (swept V t)) ℤ)
    {A B : DerivedCategory (sheaves Threefold)}
    (a : A ⟶ DerivedCategory.Q.obj (supportedComplex C))
    (b : DerivedCategory.Q.obj (supportedComplex C) ⟶ B) :
    functionStalk.mapDerivedCategory.map (a ≫ b) = 0 := by
  rw [Functor.map_comp, (derivedStalk_zero hd C).eq_of_tgt (functionStalk.mapDerivedCategory.map a) 0,
    zero_comp]

end CycleQ2GenericSweptDerivedStalk
end

#print axioms CycleQ2GenericSweptDerivedStalk.derivedStalk_factor_zero
