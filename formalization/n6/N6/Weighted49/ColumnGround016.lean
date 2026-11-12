import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column128Clearing_ne_zero : column128Clearing ≠ 0 := by decide +kernel
theorem column128Checked : zero (N6.SparseProductReduce.reduceProducts column128Pairs) = true := by decide +kernel
#print axioms column128Checked
theorem column129Clearing_ne_zero : column129Clearing ≠ 0 := by decide +kernel
theorem column129Checked : zero (N6.SparseProductReduce.reduceProducts column129Pairs) = true := by decide +kernel
#print axioms column129Checked
theorem column130Clearing_ne_zero : column130Clearing ≠ 0 := by decide +kernel
theorem column130Checked : zero (N6.SparseProductReduce.reduceProducts column130Pairs) = true := by decide +kernel
#print axioms column130Checked
theorem column131Clearing_ne_zero : column131Clearing ≠ 0 := by decide +kernel
theorem column131Checked : zero (N6.SparseProductReduce.reduceProducts column131Pairs) = true := by decide +kernel
#print axioms column131Checked
theorem column132Clearing_ne_zero : column132Clearing ≠ 0 := by decide +kernel
theorem column132Checked : zero (N6.SparseProductReduce.reduceProducts column132Pairs) = true := by decide +kernel
#print axioms column132Checked
theorem column133Clearing_ne_zero : column133Clearing ≠ 0 := by decide +kernel
theorem column133Checked : zero (N6.SparseProductReduce.reduceProducts column133Pairs) = true := by decide +kernel
#print axioms column133Checked
theorem column134Clearing_ne_zero : column134Clearing ≠ 0 := by decide +kernel
theorem column134Checked : zero (N6.SparseProductReduce.reduceProducts column134Pairs) = true := by decide +kernel
#print axioms column134Checked
theorem column135Clearing_ne_zero : column135Clearing ≠ 0 := by decide +kernel
theorem column135Checked : zero (N6.SparseProductReduce.reduceProducts column135Pairs) = true := by decide +kernel
#print axioms column135Checked
end N6.Weighted49
