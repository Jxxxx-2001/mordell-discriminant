import N6.Weighted49.LexData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem row_P35L_nonzero : row_P35L ≠ 0 := by decide +kernel
theorem row_P35ZeroListChecked : foldColumns 49 row_P35WeightsData.toList row_P35ColumnsList = List.replicate 49 0 := by decide +kernel
theorem row_P35WeightsChecked : ∀ j : Fin 36, row_P35Gcd * row_P35Weights j * row_P35Dens j = row_P35L * row_P35Coefficients j := by decide +kernel
#print axioms row_P35ZeroListChecked
#print axioms row_P35WeightsChecked
end N6.Weighted49
