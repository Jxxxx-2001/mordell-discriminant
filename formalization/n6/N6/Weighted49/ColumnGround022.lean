import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column176Clearing_ne_zero : column176Clearing ≠ 0 := by decide +kernel
theorem column176Checked : zero (N6.SparseProductReduce.reduceProducts column176Pairs) = true := by decide +kernel
#print axioms column176Checked
theorem column177Clearing_ne_zero : column177Clearing ≠ 0 := by decide +kernel
theorem column177Checked : zero (N6.SparseProductReduce.reduceProducts column177Pairs) = true := by decide +kernel
#print axioms column177Checked
theorem column178Clearing_ne_zero : column178Clearing ≠ 0 := by decide +kernel
theorem column178Checked : zero (N6.SparseProductReduce.reduceProducts column178Pairs) = true := by decide +kernel
#print axioms column178Checked
theorem column179Clearing_ne_zero : column179Clearing ≠ 0 := by decide +kernel
theorem column179Checked : zero (N6.SparseProductReduce.reduceProducts column179Pairs) = true := by decide +kernel
#print axioms column179Checked
theorem column180Clearing_ne_zero : column180Clearing ≠ 0 := by decide +kernel
theorem column180Checked : zero (N6.SparseProductReduce.reduceProducts column180Pairs) = true := by decide +kernel
#print axioms column180Checked
theorem column181Clearing_ne_zero : column181Clearing ≠ 0 := by decide +kernel
theorem column181Checked : zero (N6.SparseProductReduce.reduceProducts column181Pairs) = true := by decide +kernel
#print axioms column181Checked
theorem column182Clearing_ne_zero : column182Clearing ≠ 0 := by decide +kernel
theorem column182Checked : zero (N6.SparseProductReduce.reduceProducts column182Pairs) = true := by decide +kernel
#print axioms column182Checked
theorem column183Clearing_ne_zero : column183Clearing ≠ 0 := by decide +kernel
theorem column183Checked : zero (N6.SparseProductReduce.reduceProducts column183Pairs) = true := by decide +kernel
#print axioms column183Checked
end N6.Weighted49
