import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column112Clearing_ne_zero : column112Clearing ≠ 0 := by decide +kernel
theorem column112Checked : zero (N6.SparseProductReduce.reduceProducts column112Pairs) = true := by decide +kernel
#print axioms column112Checked
theorem column113Clearing_ne_zero : column113Clearing ≠ 0 := by decide +kernel
theorem column113Checked : zero (N6.SparseProductReduce.reduceProducts column113Pairs) = true := by decide +kernel
#print axioms column113Checked
theorem column114Clearing_ne_zero : column114Clearing ≠ 0 := by decide +kernel
theorem column114Checked : zero (N6.SparseProductReduce.reduceProducts column114Pairs) = true := by decide +kernel
#print axioms column114Checked
theorem column115Clearing_ne_zero : column115Clearing ≠ 0 := by decide +kernel
theorem column115Checked : zero (N6.SparseProductReduce.reduceProducts column115Pairs) = true := by decide +kernel
#print axioms column115Checked
theorem column116Clearing_ne_zero : column116Clearing ≠ 0 := by decide +kernel
theorem column116Checked : zero (N6.SparseProductReduce.reduceProducts column116Pairs) = true := by decide +kernel
#print axioms column116Checked
theorem column117Clearing_ne_zero : column117Clearing ≠ 0 := by decide +kernel
theorem column117Checked : zero (N6.SparseProductReduce.reduceProducts column117Pairs) = true := by decide +kernel
#print axioms column117Checked
theorem column118Clearing_ne_zero : column118Clearing ≠ 0 := by decide +kernel
theorem column118Checked : zero (N6.SparseProductReduce.reduceProducts column118Pairs) = true := by decide +kernel
#print axioms column118Checked
theorem column119Clearing_ne_zero : column119Clearing ≠ 0 := by decide +kernel
theorem column119Checked : zero (N6.SparseProductReduce.reduceProducts column119Pairs) = true := by decide +kernel
#print axioms column119Checked
end N6.Weighted49
