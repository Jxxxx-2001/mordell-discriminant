import N6.Weighted49.LexData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem row_eL_nonzero : row_eL ≠ 0 := by decide +kernel
theorem row_eZeroListChecked : foldColumns 49 row_eWeightsData.toList row_eColumnsList = List.replicate 49 0 := by decide +kernel
theorem row_eWeightsChecked : ∀ j : Fin 36, row_eGcd * row_eWeights j * row_eDens j = row_eL * row_eCoefficients j := by decide +kernel
theorem row_eCoeffCastSucc : ∀ j : Fin 35, row_eCoefficients j.castSucc = lex_eH j := by decide +kernel
theorem row_eCoeffLast : row_eCoefficients (Fin.last 35) = lex_eA := by decide +kernel
#print axioms row_eZeroListChecked
#print axioms row_eWeightsChecked
end N6.Weighted49
