import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column152Clearing_ne_zero : column152Clearing ≠ 0 := by decide +kernel
theorem column152Checked : zero (N6.SparseProductReduce.reduceProducts column152Pairs) = true := by decide +kernel
#print axioms column152Checked
theorem column153Clearing_ne_zero : column153Clearing ≠ 0 := by decide +kernel
theorem column153Checked : zero (N6.SparseProductReduce.reduceProducts column153Pairs) = true := by decide +kernel
#print axioms column153Checked
theorem column154Clearing_ne_zero : column154Clearing ≠ 0 := by decide +kernel
theorem column154Checked : zero (N6.SparseProductReduce.reduceProducts column154Pairs) = true := by decide +kernel
#print axioms column154Checked
theorem column155Clearing_ne_zero : column155Clearing ≠ 0 := by decide +kernel
theorem column155Checked : zero (N6.SparseProductReduce.reduceProducts column155Pairs) = true := by decide +kernel
#print axioms column155Checked
theorem column156Clearing_ne_zero : column156Clearing ≠ 0 := by decide +kernel
theorem column156Checked : zero (N6.SparseProductReduce.reduceProducts column156Pairs) = true := by decide +kernel
#print axioms column156Checked
theorem column157Clearing_ne_zero : column157Clearing ≠ 0 := by decide +kernel
theorem column157Checked : zero (N6.SparseProductReduce.reduceProducts column157Pairs) = true := by decide +kernel
#print axioms column157Checked
theorem column158Clearing_ne_zero : column158Clearing ≠ 0 := by decide +kernel
theorem column158Checked : zero (N6.SparseProductReduce.reduceProducts column158Pairs) = true := by decide +kernel
#print axioms column158Checked
theorem column159Clearing_ne_zero : column159Clearing ≠ 0 := by decide +kernel
theorem column159Checked : zero (N6.SparseProductReduce.reduceProducts column159Pairs) = true := by decide +kernel
#print axioms column159Checked
end N6.Weighted49
