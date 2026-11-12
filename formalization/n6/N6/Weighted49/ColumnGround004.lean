import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column032Clearing_ne_zero : column032Clearing ≠ 0 := by decide +kernel
theorem column032Checked : zero (N6.SparseProductReduce.reduceProducts column032Pairs) = true := by decide +kernel
#print axioms column032Checked
theorem column033Clearing_ne_zero : column033Clearing ≠ 0 := by decide +kernel
theorem column033Checked : zero (N6.SparseProductReduce.reduceProducts column033Pairs) = true := by decide +kernel
#print axioms column033Checked
theorem column034Clearing_ne_zero : column034Clearing ≠ 0 := by decide +kernel
theorem column034Checked : zero (N6.SparseProductReduce.reduceProducts column034Pairs) = true := by decide +kernel
#print axioms column034Checked
theorem column035Clearing_ne_zero : column035Clearing ≠ 0 := by decide +kernel
theorem column035Checked : zero (N6.SparseProductReduce.reduceProducts column035Pairs) = true := by decide +kernel
#print axioms column035Checked
theorem column036Clearing_ne_zero : column036Clearing ≠ 0 := by decide +kernel
theorem column036Checked : zero (N6.SparseProductReduce.reduceProducts column036Pairs) = true := by decide +kernel
#print axioms column036Checked
theorem column037Clearing_ne_zero : column037Clearing ≠ 0 := by decide +kernel
theorem column037Checked : zero (N6.SparseProductReduce.reduceProducts column037Pairs) = true := by decide +kernel
#print axioms column037Checked
theorem column038Clearing_ne_zero : column038Clearing ≠ 0 := by decide +kernel
theorem column038Checked : zero (N6.SparseProductReduce.reduceProducts column038Pairs) = true := by decide +kernel
#print axioms column038Checked
theorem column039Clearing_ne_zero : column039Clearing ≠ 0 := by decide +kernel
theorem column039Checked : zero (N6.SparseProductReduce.reduceProducts column039Pairs) = true := by decide +kernel
#print axioms column039Checked
end N6.Weighted49
