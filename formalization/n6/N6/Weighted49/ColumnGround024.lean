import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column192Clearing_ne_zero : column192Clearing ≠ 0 := by decide +kernel
theorem column192Checked : zero (N6.SparseProductReduce.reduceProducts column192Pairs) = true := by decide +kernel
#print axioms column192Checked
theorem column193Clearing_ne_zero : column193Clearing ≠ 0 := by decide +kernel
theorem column193Checked : zero (N6.SparseProductReduce.reduceProducts column193Pairs) = true := by decide +kernel
#print axioms column193Checked
theorem column194Clearing_ne_zero : column194Clearing ≠ 0 := by decide +kernel
theorem column194Checked : zero (N6.SparseProductReduce.reduceProducts column194Pairs) = true := by decide +kernel
#print axioms column194Checked
theorem column195Clearing_ne_zero : column195Clearing ≠ 0 := by decide +kernel
theorem column195Checked : zero (N6.SparseProductReduce.reduceProducts column195Pairs) = true := by decide +kernel
#print axioms column195Checked
end N6.Weighted49
