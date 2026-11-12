import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column008Clearing_ne_zero : column008Clearing ≠ 0 := by decide +kernel
theorem column008Checked : zero (N6.SparseProductReduce.reduceProducts column008Pairs) = true := by decide +kernel
#print axioms column008Checked
theorem column009Clearing_ne_zero : column009Clearing ≠ 0 := by decide +kernel
theorem column009Checked : zero (N6.SparseProductReduce.reduceProducts column009Pairs) = true := by decide +kernel
#print axioms column009Checked
theorem column010Clearing_ne_zero : column010Clearing ≠ 0 := by decide +kernel
theorem column010Checked : zero (N6.SparseProductReduce.reduceProducts column010Pairs) = true := by decide +kernel
#print axioms column010Checked
theorem column011Clearing_ne_zero : column011Clearing ≠ 0 := by decide +kernel
theorem column011Checked : zero (N6.SparseProductReduce.reduceProducts column011Pairs) = true := by decide +kernel
#print axioms column011Checked
theorem column012Clearing_ne_zero : column012Clearing ≠ 0 := by decide +kernel
theorem column012Checked : zero (N6.SparseProductReduce.reduceProducts column012Pairs) = true := by decide +kernel
#print axioms column012Checked
theorem column013Clearing_ne_zero : column013Clearing ≠ 0 := by decide +kernel
theorem column013Checked : zero (N6.SparseProductReduce.reduceProducts column013Pairs) = true := by decide +kernel
#print axioms column013Checked
theorem column014Clearing_ne_zero : column014Clearing ≠ 0 := by decide +kernel
theorem column014Checked : zero (N6.SparseProductReduce.reduceProducts column014Pairs) = true := by decide +kernel
#print axioms column014Checked
theorem column015Clearing_ne_zero : column015Clearing ≠ 0 := by decide +kernel
theorem column015Checked : zero (N6.SparseProductReduce.reduceProducts column015Pairs) = true := by decide +kernel
#print axioms column015Checked
end N6.Weighted49
