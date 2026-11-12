import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column056Clearing_ne_zero : column056Clearing ≠ 0 := by decide +kernel
theorem column056Checked : zero (N6.SparseProductReduce.reduceProducts column056Pairs) = true := by decide +kernel
#print axioms column056Checked
theorem column057Clearing_ne_zero : column057Clearing ≠ 0 := by decide +kernel
theorem column057Checked : zero (N6.SparseProductReduce.reduceProducts column057Pairs) = true := by decide +kernel
#print axioms column057Checked
theorem column058Clearing_ne_zero : column058Clearing ≠ 0 := by decide +kernel
theorem column058Checked : zero (N6.SparseProductReduce.reduceProducts column058Pairs) = true := by decide +kernel
#print axioms column058Checked
theorem column059Clearing_ne_zero : column059Clearing ≠ 0 := by decide +kernel
theorem column059Checked : zero (N6.SparseProductReduce.reduceProducts column059Pairs) = true := by decide +kernel
#print axioms column059Checked
theorem column060Clearing_ne_zero : column060Clearing ≠ 0 := by decide +kernel
theorem column060Checked : zero (N6.SparseProductReduce.reduceProducts column060Pairs) = true := by decide +kernel
#print axioms column060Checked
theorem column061Clearing_ne_zero : column061Clearing ≠ 0 := by decide +kernel
theorem column061Checked : zero (N6.SparseProductReduce.reduceProducts column061Pairs) = true := by decide +kernel
#print axioms column061Checked
theorem column062Clearing_ne_zero : column062Clearing ≠ 0 := by decide +kernel
theorem column062Checked : zero (N6.SparseProductReduce.reduceProducts column062Pairs) = true := by decide +kernel
#print axioms column062Checked
theorem column063Clearing_ne_zero : column063Clearing ≠ 0 := by decide +kernel
theorem column063Checked : zero (N6.SparseProductReduce.reduceProducts column063Pairs) = true := by decide +kernel
#print axioms column063Checked
end N6.Weighted49
