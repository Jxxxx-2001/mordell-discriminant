import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column160Clearing_ne_zero : column160Clearing ≠ 0 := by decide +kernel
theorem column160Checked : zero (N6.SparseProductReduce.reduceProducts column160Pairs) = true := by decide +kernel
#print axioms column160Checked
theorem column161Clearing_ne_zero : column161Clearing ≠ 0 := by decide +kernel
theorem column161Checked : zero (N6.SparseProductReduce.reduceProducts column161Pairs) = true := by decide +kernel
#print axioms column161Checked
theorem column162Clearing_ne_zero : column162Clearing ≠ 0 := by decide +kernel
theorem column162Checked : zero (N6.SparseProductReduce.reduceProducts column162Pairs) = true := by decide +kernel
#print axioms column162Checked
theorem column163Clearing_ne_zero : column163Clearing ≠ 0 := by decide +kernel
theorem column163Checked : zero (N6.SparseProductReduce.reduceProducts column163Pairs) = true := by decide +kernel
#print axioms column163Checked
theorem column164Clearing_ne_zero : column164Clearing ≠ 0 := by decide +kernel
theorem column164Checked : zero (N6.SparseProductReduce.reduceProducts column164Pairs) = true := by decide +kernel
#print axioms column164Checked
theorem column165Clearing_ne_zero : column165Clearing ≠ 0 := by decide +kernel
theorem column165Checked : zero (N6.SparseProductReduce.reduceProducts column165Pairs) = true := by decide +kernel
#print axioms column165Checked
theorem column166Clearing_ne_zero : column166Clearing ≠ 0 := by decide +kernel
theorem column166Checked : zero (N6.SparseProductReduce.reduceProducts column166Pairs) = true := by decide +kernel
#print axioms column166Checked
theorem column167Clearing_ne_zero : column167Clearing ≠ 0 := by decide +kernel
theorem column167Checked : zero (N6.SparseProductReduce.reduceProducts column167Pairs) = true := by decide +kernel
#print axioms column167Checked
end N6.Weighted49
