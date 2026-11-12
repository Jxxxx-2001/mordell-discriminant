import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column184Clearing_ne_zero : column184Clearing ≠ 0 := by decide +kernel
theorem column184Checked : zero (N6.SparseProductReduce.reduceProducts column184Pairs) = true := by decide +kernel
#print axioms column184Checked
theorem column185Clearing_ne_zero : column185Clearing ≠ 0 := by decide +kernel
theorem column185Checked : zero (N6.SparseProductReduce.reduceProducts column185Pairs) = true := by decide +kernel
#print axioms column185Checked
theorem column186Clearing_ne_zero : column186Clearing ≠ 0 := by decide +kernel
theorem column186Checked : zero (N6.SparseProductReduce.reduceProducts column186Pairs) = true := by decide +kernel
#print axioms column186Checked
theorem column187Clearing_ne_zero : column187Clearing ≠ 0 := by decide +kernel
theorem column187Checked : zero (N6.SparseProductReduce.reduceProducts column187Pairs) = true := by decide +kernel
#print axioms column187Checked
theorem column188Clearing_ne_zero : column188Clearing ≠ 0 := by decide +kernel
theorem column188Checked : zero (N6.SparseProductReduce.reduceProducts column188Pairs) = true := by decide +kernel
#print axioms column188Checked
theorem column189Clearing_ne_zero : column189Clearing ≠ 0 := by decide +kernel
theorem column189Checked : zero (N6.SparseProductReduce.reduceProducts column189Pairs) = true := by decide +kernel
#print axioms column189Checked
theorem column190Clearing_ne_zero : column190Clearing ≠ 0 := by decide +kernel
theorem column190Checked : zero (N6.SparseProductReduce.reduceProducts column190Pairs) = true := by decide +kernel
#print axioms column190Checked
theorem column191Clearing_ne_zero : column191Clearing ≠ 0 := by decide +kernel
theorem column191Checked : zero (N6.SparseProductReduce.reduceProducts column191Pairs) = true := by decide +kernel
#print axioms column191Checked
end N6.Weighted49
