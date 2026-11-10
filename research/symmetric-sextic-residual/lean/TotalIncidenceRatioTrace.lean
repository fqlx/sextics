import TotalIncidenceTrace

noncomputable section
namespace ActualTotalIncidence
open SymmetricAffineField SymmetricPrimitiveEndpoint SymmetricRatioCurrent
set_option maxHeartbeats 4000000
set_option maxRecDepth 16384
set_option backward.isDefEq.respectTransparency false
attribute [local irreducible] StrengthenedContactCover.equations SymmetricContactField.equations

/-- Ratio-chart version, retaining the exact negative volume Jacobian.
The actual total source trace equality remains an explicit hypothesis. -/
def relativePrimitiveOfTotalRatioSource
    (E : Fin 3 → Derivation ℤ Algebra Algebra)
    (comp : ∀ (i : Fin 3) (x : FunctionField), E i (algebraMap FunctionField Algebra x) =
      algebraMap FunctionField Algebra (ratioTangent i x))
    (w : Fin 3 → Algebra) (source : Algebra)
    (equation : (∑ i, E i (w i)) = source)
    (htrace : totalTrace source = -t*residueDensity) : RelativePrimitive where
  coefficient := toChart (fun i => totalTrace (w i))
  differential_eq := by
    have hd : (∑ i, ratioTangent i (totalTrace (w i))) = totalTrace source := by
      calc
        _ = ∑ i, totalTrace (E i (w i)) := by
          apply Finset.sum_congr rfl
          intro i _
          exact (LocalizedIncidenceTotal.trace_derivation SymmetricContactField.Base
            FunctionField StrengthenedContactCover.equations
            (ratioTangent i) (E i) (fun x => comp i x) (w i)).symm
        _ = totalTrace (∑ i, E i (w i)) := (map_sum totalTrace _ _).symm
        _ = _ := by rw [equation]
    rw [toChart_divergence, hd, htrace]
    field_simp [t_nonzero]

#print axioms relativePrimitiveOfTotalRatioSource
end ActualTotalIncidence
