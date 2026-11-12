import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column104Clearing_ne_zero : column104Clearing ≠ 0 := by decide +kernel
theorem column104Checked : zero (N6.SparseProductReduce.reduceProducts column104Pairs) = true := by decide +kernel
#print axioms column104Checked
theorem column105Clearing_ne_zero : column105Clearing ≠ 0 := by decide +kernel
theorem column105Checked : zero (N6.SparseProductReduce.reduceProducts column105Pairs) = true := by decide +kernel
#print axioms column105Checked
theorem column106Clearing_ne_zero : column106Clearing ≠ 0 := by decide +kernel
theorem column106Checked : zero (N6.SparseProductReduce.reduceProducts column106Pairs) = true := by decide +kernel
#print axioms column106Checked
theorem column107Clearing_ne_zero : column107Clearing ≠ 0 := by decide +kernel
theorem column107Checked : zero (N6.SparseProductReduce.reduceProducts column107Pairs) = true := by decide +kernel
#print axioms column107Checked
theorem column108Clearing_ne_zero : column108Clearing ≠ 0 := by decide +kernel
theorem column108Checked : zero (N6.SparseProductReduce.reduceProducts column108Pairs) = true := by decide +kernel
#print axioms column108Checked
theorem column109Clearing_ne_zero : column109Clearing ≠ 0 := by decide +kernel
theorem column109Checked : zero (N6.SparseProductReduce.reduceProducts column109Pairs) = true := by decide +kernel
#print axioms column109Checked
theorem column110Clearing_ne_zero : column110Clearing ≠ 0 := by decide +kernel
theorem column110Checked : zero (N6.SparseProductReduce.reduceProducts column110Pairs) = true := by decide +kernel
#print axioms column110Checked
theorem column111Clearing_ne_zero : column111Clearing ≠ 0 := by decide +kernel
theorem column111Checked : zero (N6.SparseProductReduce.reduceProducts column111Pairs) = true := by decide +kernel
#print axioms column111Checked
end N6.Weighted49
