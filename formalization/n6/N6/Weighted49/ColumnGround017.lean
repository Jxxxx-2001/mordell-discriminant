import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column136Clearing_ne_zero : column136Clearing ≠ 0 := by decide +kernel
theorem column136Checked : zero (N6.SparseProductReduce.reduceProducts column136Pairs) = true := by decide +kernel
#print axioms column136Checked
theorem column137Clearing_ne_zero : column137Clearing ≠ 0 := by decide +kernel
theorem column137Checked : zero (N6.SparseProductReduce.reduceProducts column137Pairs) = true := by decide +kernel
#print axioms column137Checked
theorem column138Clearing_ne_zero : column138Clearing ≠ 0 := by decide +kernel
theorem column138Checked : zero (N6.SparseProductReduce.reduceProducts column138Pairs) = true := by decide +kernel
#print axioms column138Checked
theorem column139Clearing_ne_zero : column139Clearing ≠ 0 := by decide +kernel
theorem column139Checked : zero (N6.SparseProductReduce.reduceProducts column139Pairs) = true := by decide +kernel
#print axioms column139Checked
theorem column140Clearing_ne_zero : column140Clearing ≠ 0 := by decide +kernel
theorem column140Checked : zero (N6.SparseProductReduce.reduceProducts column140Pairs) = true := by decide +kernel
#print axioms column140Checked
theorem column141Clearing_ne_zero : column141Clearing ≠ 0 := by decide +kernel
theorem column141Checked : zero (N6.SparseProductReduce.reduceProducts column141Pairs) = true := by decide +kernel
#print axioms column141Checked
theorem column142Clearing_ne_zero : column142Clearing ≠ 0 := by decide +kernel
theorem column142Checked : zero (N6.SparseProductReduce.reduceProducts column142Pairs) = true := by decide +kernel
#print axioms column142Checked
theorem column143Clearing_ne_zero : column143Clearing ≠ 0 := by decide +kernel
theorem column143Checked : zero (N6.SparseProductReduce.reduceProducts column143Pairs) = true := by decide +kernel
#print axioms column143Checked
end N6.Weighted49
