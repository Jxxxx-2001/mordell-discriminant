import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column072Clearing_ne_zero : column072Clearing ≠ 0 := by decide +kernel
theorem column072Checked : zero (N6.SparseProductReduce.reduceProducts column072Pairs) = true := by decide +kernel
#print axioms column072Checked
theorem column073Clearing_ne_zero : column073Clearing ≠ 0 := by decide +kernel
theorem column073Checked : zero (N6.SparseProductReduce.reduceProducts column073Pairs) = true := by decide +kernel
#print axioms column073Checked
theorem column074Clearing_ne_zero : column074Clearing ≠ 0 := by decide +kernel
theorem column074Checked : zero (N6.SparseProductReduce.reduceProducts column074Pairs) = true := by decide +kernel
#print axioms column074Checked
theorem column075Clearing_ne_zero : column075Clearing ≠ 0 := by decide +kernel
theorem column075Checked : zero (N6.SparseProductReduce.reduceProducts column075Pairs) = true := by decide +kernel
#print axioms column075Checked
theorem column076Clearing_ne_zero : column076Clearing ≠ 0 := by decide +kernel
theorem column076Checked : zero (N6.SparseProductReduce.reduceProducts column076Pairs) = true := by decide +kernel
#print axioms column076Checked
theorem column077Clearing_ne_zero : column077Clearing ≠ 0 := by decide +kernel
theorem column077Checked : zero (N6.SparseProductReduce.reduceProducts column077Pairs) = true := by decide +kernel
#print axioms column077Checked
theorem column078Clearing_ne_zero : column078Clearing ≠ 0 := by decide +kernel
theorem column078Checked : zero (N6.SparseProductReduce.reduceProducts column078Pairs) = true := by decide +kernel
#print axioms column078Checked
theorem column079Clearing_ne_zero : column079Clearing ≠ 0 := by decide +kernel
theorem column079Checked : zero (N6.SparseProductReduce.reduceProducts column079Pairs) = true := by decide +kernel
#print axioms column079Checked
end N6.Weighted49
