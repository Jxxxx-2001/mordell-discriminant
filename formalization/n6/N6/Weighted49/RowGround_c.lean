import N6.Weighted49.LexData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem row_cL_nonzero : row_cL ≠ 0 := by decide +kernel
theorem row_cZeroListChecked : foldColumns 49 row_cWeightsData.toList row_cColumnsList = List.replicate 49 0 := by decide +kernel
theorem row_cWeightsChecked : ∀ j : Fin 36, row_cGcd * row_cWeights j * row_cDens j = row_cL * row_cCoefficients j := by decide +kernel
theorem row_cCoeffCastSucc : ∀ j : Fin 35, row_cCoefficients j.castSucc = lex_cH j := by decide +kernel
theorem row_cCoeffLast : row_cCoefficients (Fin.last 35) = lex_cA := by decide +kernel
#print axioms row_cZeroListChecked
#print axioms row_cWeightsChecked
end N6.Weighted49
