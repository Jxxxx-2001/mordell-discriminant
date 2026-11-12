import N6.Weighted49.LexData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem row_kL_nonzero : row_kL ≠ 0 := by decide +kernel
theorem row_kZeroListChecked : foldColumns 49 row_kWeightsData.toList row_kColumnsList = List.replicate 49 0 := by decide +kernel
theorem row_kWeightsChecked : ∀ j : Fin 36, row_kGcd * row_kWeights j * row_kDens j = row_kL * row_kCoefficients j := by decide +kernel
theorem row_kCoeffCastSucc : ∀ j : Fin 35, row_kCoefficients j.castSucc = lex_kH j := by decide +kernel
theorem row_kCoeffLast : row_kCoefficients (Fin.last 35) = lex_kA := by decide +kernel
#print axioms row_kZeroListChecked
#print axioms row_kWeightsChecked
end N6.Weighted49
