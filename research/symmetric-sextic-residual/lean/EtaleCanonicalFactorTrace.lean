import EtaleFactorAssembly
import EtaleProductTrace
import TotalIncidenceCompatibility

noncomputable section
open scoped BigOperators
namespace EtaleDerivationLift
set_option maxHeartbeats 4000000
variable (K A : Type*) [Field K] [CommRing A] [Algebra K A]
    [IsArtinianRing A] [IsReduced A] [Module.Finite K A]
    [Fintype (MaximalSpectrum A)]
local instance factor_field (m : MaximalSpectrum A) : Field (A ⧸ m.asIdeal) :=
  Ideal.Quotient.field _

/-- The canonical decomposition uses all maximal factors of the full algebra. -/
def factorEquiv : A ≃ₐ[K] (∀ m : MaximalSpectrum A, A ⧸ m.asIdeal) :=
  (IsArtinianRing.equivPi A).restrictScalars K

/-- Each factor contributes its ordinary trace, counted with its full degree. -/
theorem trace_all_factors (x : A) :
    Algebra.trace K A x =
      ∑ m : MaximalSpectrum A, Algebra.trace K (A ⧸ m.asIdeal) (Ideal.Quotient.mk m.asIdeal x) := by
  classical
  simpa only [factorEquiv, AlgEquiv.restrictScalars_apply, IsArtinianRing.equivPi_apply] using
    EtaleProductTrace.trace_of_algEquiv (K := K)
    (fun m : MaximalSpectrum A => A ⧸ m.asIdeal) (factorEquiv K A) x

#print axioms factorEquiv
#print axioms trace_all_factors
end EtaleDerivationLift

namespace ActualTotalIncidence
open SymmetricAffineField
attribute [local irreducible] StrengthenedContactCover.equations SymmetricContactField.equations
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
local instance total_artinian : IsArtinianRing Algebra := IsArtinianRing.of_finite FunctionField Algebra
local instance total_reduced : IsReduced Algebra :=
  _root_.Algebra.FormallyUnramified.isReduced_of_field FunctionField Algebra
local instance total_factors_fintype : Fintype (MaximalSpectrum Algebra) := Fintype.ofFinite _
local instance factor_field (m : MaximalSpectrum Algebra) : Field (Algebra ⧸ m.asIdeal) :=
  Ideal.Quotient.field _

theorem totalTrace_all_factors (x : Algebra) :
    totalTrace x = (Module.finrank FunctionField Algebra : FunctionField)⁻¹ *
      ∑ m : MaximalSpectrum Algebra, Algebra.trace FunctionField (Algebra ⧸ m.asIdeal)
        (Ideal.Quotient.mk m.asIdeal x) := by
  change (Fintype.card (Fin (Module.finrank FunctionField Algebra)) : FunctionField)⁻¹ *
    Algebra.trace FunctionField Algebra x = _
  rw [Fintype.card_fin,EtaleDerivationLift.trace_all_factors FunctionField Algebra]

#print axioms totalTrace_all_factors
end ActualTotalIncidence
