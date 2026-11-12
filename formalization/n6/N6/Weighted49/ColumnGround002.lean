import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column016Clearing_ne_zero : column016Clearing ≠ 0 := by decide +kernel
theorem column016Checked : zero (N6.SparseProductReduce.reduceProducts column016Pairs) = true := by decide +kernel
#print axioms column016Checked
theorem column017Clearing_ne_zero : column017Clearing ≠ 0 := by decide +kernel
theorem column017Checked : zero (N6.SparseProductReduce.reduceProducts column017Pairs) = true := by decide +kernel
#print axioms column017Checked
theorem column018Clearing_ne_zero : column018Clearing ≠ 0 := by decide +kernel
theorem column018Checked : zero (N6.SparseProductReduce.reduceProducts column018Pairs) = true := by decide +kernel
#print axioms column018Checked
theorem column019Clearing_ne_zero : column019Clearing ≠ 0 := by decide +kernel
theorem column019Checked : zero (N6.SparseProductReduce.reduceProducts column019Pairs) = true := by decide +kernel
#print axioms column019Checked
theorem column020Clearing_ne_zero : column020Clearing ≠ 0 := by decide +kernel
theorem column020Checked : zero (N6.SparseProductReduce.reduceProducts column020Pairs) = true := by decide +kernel
#print axioms column020Checked
theorem column021Clearing_ne_zero : column021Clearing ≠ 0 := by decide +kernel
theorem column021Checked : zero (N6.SparseProductReduce.reduceProducts column021Pairs) = true := by decide +kernel
#print axioms column021Checked
theorem column022Clearing_ne_zero : column022Clearing ≠ 0 := by decide +kernel
theorem column022Checked : zero (N6.SparseProductReduce.reduceProducts column022Pairs) = true := by decide +kernel
#print axioms column022Checked
theorem column023Clearing_ne_zero : column023Clearing ≠ 0 := by decide +kernel
theorem column023Checked : zero (N6.SparseProductReduce.reduceProducts column023Pairs) = true := by decide +kernel
#print axioms column023Checked
end N6.Weighted49
