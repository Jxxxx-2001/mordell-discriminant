import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column144Clearing_ne_zero : column144Clearing ≠ 0 := by decide +kernel
theorem column144Checked : zero (N6.SparseProductReduce.reduceProducts column144Pairs) = true := by decide +kernel
#print axioms column144Checked
theorem column145Clearing_ne_zero : column145Clearing ≠ 0 := by decide +kernel
theorem column145Checked : zero (N6.SparseProductReduce.reduceProducts column145Pairs) = true := by decide +kernel
#print axioms column145Checked
theorem column146Clearing_ne_zero : column146Clearing ≠ 0 := by decide +kernel
theorem column146Checked : zero (N6.SparseProductReduce.reduceProducts column146Pairs) = true := by decide +kernel
#print axioms column146Checked
theorem column147Clearing_ne_zero : column147Clearing ≠ 0 := by decide +kernel
theorem column147Checked : zero (N6.SparseProductReduce.reduceProducts column147Pairs) = true := by decide +kernel
#print axioms column147Checked
theorem column148Clearing_ne_zero : column148Clearing ≠ 0 := by decide +kernel
theorem column148Checked : zero (N6.SparseProductReduce.reduceProducts column148Pairs) = true := by decide +kernel
#print axioms column148Checked
theorem column149Clearing_ne_zero : column149Clearing ≠ 0 := by decide +kernel
theorem column149Checked : zero (N6.SparseProductReduce.reduceProducts column149Pairs) = true := by decide +kernel
#print axioms column149Checked
theorem column150Clearing_ne_zero : column150Clearing ≠ 0 := by decide +kernel
theorem column150Checked : zero (N6.SparseProductReduce.reduceProducts column150Pairs) = true := by decide +kernel
#print axioms column150Checked
theorem column151Clearing_ne_zero : column151Clearing ≠ 0 := by decide +kernel
theorem column151Checked : zero (N6.SparseProductReduce.reduceProducts column151Pairs) = true := by decide +kernel
#print axioms column151Checked
end N6.Weighted49
