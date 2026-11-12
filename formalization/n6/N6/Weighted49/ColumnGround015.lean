import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column120Clearing_ne_zero : column120Clearing ≠ 0 := by decide +kernel
theorem column120Checked : zero (N6.SparseProductReduce.reduceProducts column120Pairs) = true := by decide +kernel
#print axioms column120Checked
theorem column121Clearing_ne_zero : column121Clearing ≠ 0 := by decide +kernel
theorem column121Checked : zero (N6.SparseProductReduce.reduceProducts column121Pairs) = true := by decide +kernel
#print axioms column121Checked
theorem column122Clearing_ne_zero : column122Clearing ≠ 0 := by decide +kernel
theorem column122Checked : zero (N6.SparseProductReduce.reduceProducts column122Pairs) = true := by decide +kernel
#print axioms column122Checked
theorem column123Clearing_ne_zero : column123Clearing ≠ 0 := by decide +kernel
theorem column123Checked : zero (N6.SparseProductReduce.reduceProducts column123Pairs) = true := by decide +kernel
#print axioms column123Checked
theorem column124Clearing_ne_zero : column124Clearing ≠ 0 := by decide +kernel
theorem column124Checked : zero (N6.SparseProductReduce.reduceProducts column124Pairs) = true := by decide +kernel
#print axioms column124Checked
theorem column125Clearing_ne_zero : column125Clearing ≠ 0 := by decide +kernel
theorem column125Checked : zero (N6.SparseProductReduce.reduceProducts column125Pairs) = true := by decide +kernel
#print axioms column125Checked
theorem column126Clearing_ne_zero : column126Clearing ≠ 0 := by decide +kernel
theorem column126Checked : zero (N6.SparseProductReduce.reduceProducts column126Pairs) = true := by decide +kernel
#print axioms column126Checked
theorem column127Clearing_ne_zero : column127Clearing ≠ 0 := by decide +kernel
theorem column127Checked : zero (N6.SparseProductReduce.reduceProducts column127Pairs) = true := by decide +kernel
#print axioms column127Checked
end N6.Weighted49
