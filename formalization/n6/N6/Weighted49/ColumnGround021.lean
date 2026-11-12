import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column168Clearing_ne_zero : column168Clearing ≠ 0 := by decide +kernel
theorem column168Checked : zero (N6.SparseProductReduce.reduceProducts column168Pairs) = true := by decide +kernel
#print axioms column168Checked
theorem column169Clearing_ne_zero : column169Clearing ≠ 0 := by decide +kernel
theorem column169Checked : zero (N6.SparseProductReduce.reduceProducts column169Pairs) = true := by decide +kernel
#print axioms column169Checked
theorem column170Clearing_ne_zero : column170Clearing ≠ 0 := by decide +kernel
theorem column170Checked : zero (N6.SparseProductReduce.reduceProducts column170Pairs) = true := by decide +kernel
#print axioms column170Checked
theorem column171Clearing_ne_zero : column171Clearing ≠ 0 := by decide +kernel
theorem column171Checked : zero (N6.SparseProductReduce.reduceProducts column171Pairs) = true := by decide +kernel
#print axioms column171Checked
theorem column172Clearing_ne_zero : column172Clearing ≠ 0 := by decide +kernel
theorem column172Checked : zero (N6.SparseProductReduce.reduceProducts column172Pairs) = true := by decide +kernel
#print axioms column172Checked
theorem column173Clearing_ne_zero : column173Clearing ≠ 0 := by decide +kernel
theorem column173Checked : zero (N6.SparseProductReduce.reduceProducts column173Pairs) = true := by decide +kernel
#print axioms column173Checked
theorem column174Clearing_ne_zero : column174Clearing ≠ 0 := by decide +kernel
theorem column174Checked : zero (N6.SparseProductReduce.reduceProducts column174Pairs) = true := by decide +kernel
#print axioms column174Checked
theorem column175Clearing_ne_zero : column175Clearing ≠ 0 := by decide +kernel
theorem column175Checked : zero (N6.SparseProductReduce.reduceProducts column175Pairs) = true := by decide +kernel
#print axioms column175Checked
end N6.Weighted49
