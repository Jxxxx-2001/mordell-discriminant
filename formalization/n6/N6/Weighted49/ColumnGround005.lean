import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column040Clearing_ne_zero : column040Clearing ≠ 0 := by decide +kernel
theorem column040Checked : zero (N6.SparseProductReduce.reduceProducts column040Pairs) = true := by decide +kernel
#print axioms column040Checked
theorem column041Clearing_ne_zero : column041Clearing ≠ 0 := by decide +kernel
theorem column041Checked : zero (N6.SparseProductReduce.reduceProducts column041Pairs) = true := by decide +kernel
#print axioms column041Checked
theorem column042Clearing_ne_zero : column042Clearing ≠ 0 := by decide +kernel
theorem column042Checked : zero (N6.SparseProductReduce.reduceProducts column042Pairs) = true := by decide +kernel
#print axioms column042Checked
theorem column043Clearing_ne_zero : column043Clearing ≠ 0 := by decide +kernel
theorem column043Checked : zero (N6.SparseProductReduce.reduceProducts column043Pairs) = true := by decide +kernel
#print axioms column043Checked
theorem column044Clearing_ne_zero : column044Clearing ≠ 0 := by decide +kernel
theorem column044Checked : zero (N6.SparseProductReduce.reduceProducts column044Pairs) = true := by decide +kernel
#print axioms column044Checked
theorem column045Clearing_ne_zero : column045Clearing ≠ 0 := by decide +kernel
theorem column045Checked : zero (N6.SparseProductReduce.reduceProducts column045Pairs) = true := by decide +kernel
#print axioms column045Checked
theorem column046Clearing_ne_zero : column046Clearing ≠ 0 := by decide +kernel
theorem column046Checked : zero (N6.SparseProductReduce.reduceProducts column046Pairs) = true := by decide +kernel
#print axioms column046Checked
theorem column047Clearing_ne_zero : column047Clearing ≠ 0 := by decide +kernel
theorem column047Checked : zero (N6.SparseProductReduce.reduceProducts column047Pairs) = true := by decide +kernel
#print axioms column047Checked
end N6.Weighted49
