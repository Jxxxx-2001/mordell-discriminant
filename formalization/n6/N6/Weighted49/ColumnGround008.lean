import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column064Clearing_ne_zero : column064Clearing ≠ 0 := by decide +kernel
theorem column064Checked : zero (N6.SparseProductReduce.reduceProducts column064Pairs) = true := by decide +kernel
#print axioms column064Checked
theorem column065Clearing_ne_zero : column065Clearing ≠ 0 := by decide +kernel
theorem column065Checked : zero (N6.SparseProductReduce.reduceProducts column065Pairs) = true := by decide +kernel
#print axioms column065Checked
theorem column066Clearing_ne_zero : column066Clearing ≠ 0 := by decide +kernel
theorem column066Checked : zero (N6.SparseProductReduce.reduceProducts column066Pairs) = true := by decide +kernel
#print axioms column066Checked
theorem column067Clearing_ne_zero : column067Clearing ≠ 0 := by decide +kernel
theorem column067Checked : zero (N6.SparseProductReduce.reduceProducts column067Pairs) = true := by decide +kernel
#print axioms column067Checked
theorem column068Clearing_ne_zero : column068Clearing ≠ 0 := by decide +kernel
theorem column068Checked : zero (N6.SparseProductReduce.reduceProducts column068Pairs) = true := by decide +kernel
#print axioms column068Checked
theorem column069Clearing_ne_zero : column069Clearing ≠ 0 := by decide +kernel
theorem column069Checked : zero (N6.SparseProductReduce.reduceProducts column069Pairs) = true := by decide +kernel
#print axioms column069Checked
theorem column070Clearing_ne_zero : column070Clearing ≠ 0 := by decide +kernel
theorem column070Checked : zero (N6.SparseProductReduce.reduceProducts column070Pairs) = true := by decide +kernel
#print axioms column070Checked
theorem column071Clearing_ne_zero : column071Clearing ≠ 0 := by decide +kernel
theorem column071Checked : zero (N6.SparseProductReduce.reduceProducts column071Pairs) = true := by decide +kernel
#print axioms column071Checked
end N6.Weighted49
