import EtaleCanonicalFactorTrace

noncomputable section
namespace ActualTotalIncidence
open SymmetricAffineField SymmetricRatioCurrent SymmetricPrimitiveEndpoint HoldoutConstruction
attribute [local irreducible] StrengthenedContactCover.equations SymmetricContactField.equations
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
local instance endpoint_artinian : IsArtinianRing Algebra := IsArtinianRing.of_finite FunctionField Algebra
local instance endpoint_factors_fintype : Fintype (MaximalSpectrum Algebra) := Fintype.ofFinite _
local instance endpoint_factor_field (m : MaximalSpectrum Algebra) : Field (Algebra ⧸ m.asIdeal) :=
  Ideal.Quotient.field _

/-- Complete-factor source equations, with ordinary traces normalized once by
full algebra rank, suffice. Neither source input is supplied by this theorem. -/
def relativePrimitiveOfAllFactorSources
    (w : Fin 3 → Algebra) (source : Algebra)
    (equations : ∀ (I : Ideal Algebra) (_ : I.IsMaximal),
      letI : Field (Algebra ⧸ I) := Ideal.Quotient.field I
      (∑ i, extendFiniteDerivation (L := Algebra ⧸ I) (ratioTangent i)
        (Ideal.Quotient.mk I (w i))) = Ideal.Quotient.mk I source)
    (traceSource :
      (∑ m : MaximalSpectrum Algebra, _root_.Algebra.trace FunctionField (Algebra ⧸ m.asIdeal)
        (Ideal.Quotient.mk m.asIdeal source)) =
        (Module.finrank FunctionField Algebra : FunctionField)*(-t*residueDensity)) :
    RelativePrimitive :=
  relativePrimitiveOfLiftedTotalSource w source
    (EtaleDerivationLift.divergence_of_all_maximal_quotients ratioTangent moving
      moving_compatible w source equations) (by
        rw [totalTrace_all_factors,traceSource]
        have hn : (Module.finrank FunctionField Algebra : FunctionField) ≠ 0 :=
          Nat.cast_ne_zero.mpr (Nat.ne_of_gt totalRank_pos)
        exact inv_mul_cancel_left₀ hn _)

#print axioms relativePrimitiveOfAllFactorSources
end ActualTotalIncidence
