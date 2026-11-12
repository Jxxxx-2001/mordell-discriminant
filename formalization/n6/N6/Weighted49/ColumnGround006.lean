import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column048Clearing_ne_zero : column048Clearing ≠ 0 := by decide +kernel
theorem column048Checked : zero (N6.SparseProductReduce.reduceProducts column048Pairs) = true := by decide +kernel
#print axioms column048Checked
theorem column049Clearing_ne_zero : column049Clearing ≠ 0 := by decide +kernel
theorem column049Checked : zero (N6.SparseProductReduce.reduceProducts column049Pairs) = true := by decide +kernel
#print axioms column049Checked
theorem column050Clearing_ne_zero : column050Clearing ≠ 0 := by decide +kernel
theorem column050Checked : zero (N6.SparseProductReduce.reduceProducts column050Pairs) = true := by decide +kernel
#print axioms column050Checked
theorem column051Clearing_ne_zero : column051Clearing ≠ 0 := by decide +kernel
theorem column051Checked : zero (N6.SparseProductReduce.reduceProducts column051Pairs) = true := by decide +kernel
#print axioms column051Checked
theorem column052Clearing_ne_zero : column052Clearing ≠ 0 := by decide +kernel
theorem column052Checked : zero (N6.SparseProductReduce.reduceProducts column052Pairs) = true := by decide +kernel
#print axioms column052Checked
theorem column053Clearing_ne_zero : column053Clearing ≠ 0 := by decide +kernel
theorem column053Checked : zero (N6.SparseProductReduce.reduceProducts column053Pairs) = true := by decide +kernel
#print axioms column053Checked
theorem column054Clearing_ne_zero : column054Clearing ≠ 0 := by decide +kernel
theorem column054Checked : zero (N6.SparseProductReduce.reduceProducts column054Pairs) = true := by decide +kernel
#print axioms column054Checked
theorem column055Clearing_ne_zero : column055Clearing ≠ 0 := by decide +kernel
theorem column055Checked : zero (N6.SparseProductReduce.reduceProducts column055Pairs) = true := by decide +kernel
#print axioms column055Checked
end N6.Weighted49
