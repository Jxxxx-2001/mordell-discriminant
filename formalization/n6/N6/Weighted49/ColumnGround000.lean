import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column000Clearing_ne_zero : column000Clearing ≠ 0 := by decide +kernel
theorem column000Checked : zero (N6.SparseProductReduce.reduceProducts column000Pairs) = true := by decide +kernel
#print axioms column000Checked
theorem column001Clearing_ne_zero : column001Clearing ≠ 0 := by decide +kernel
theorem column001Checked : zero (N6.SparseProductReduce.reduceProducts column001Pairs) = true := by decide +kernel
#print axioms column001Checked
theorem column002Clearing_ne_zero : column002Clearing ≠ 0 := by decide +kernel
theorem column002Checked : zero (N6.SparseProductReduce.reduceProducts column002Pairs) = true := by decide +kernel
#print axioms column002Checked
theorem column003Clearing_ne_zero : column003Clearing ≠ 0 := by decide +kernel
theorem column003Checked : zero (N6.SparseProductReduce.reduceProducts column003Pairs) = true := by decide +kernel
#print axioms column003Checked
theorem column004Clearing_ne_zero : column004Clearing ≠ 0 := by decide +kernel
theorem column004Checked : zero (N6.SparseProductReduce.reduceProducts column004Pairs) = true := by decide +kernel
#print axioms column004Checked
theorem column005Clearing_ne_zero : column005Clearing ≠ 0 := by decide +kernel
theorem column005Checked : zero (N6.SparseProductReduce.reduceProducts column005Pairs) = true := by decide +kernel
#print axioms column005Checked
theorem column006Clearing_ne_zero : column006Clearing ≠ 0 := by decide +kernel
theorem column006Checked : zero (N6.SparseProductReduce.reduceProducts column006Pairs) = true := by decide +kernel
#print axioms column006Checked
theorem column007Clearing_ne_zero : column007Clearing ≠ 0 := by decide +kernel
theorem column007Checked : zero (N6.SparseProductReduce.reduceProducts column007Pairs) = true := by decide +kernel
#print axioms column007Checked
end N6.Weighted49
