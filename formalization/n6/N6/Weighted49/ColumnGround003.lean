import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column024Clearing_ne_zero : column024Clearing ≠ 0 := by decide +kernel
theorem column024Checked : zero (N6.SparseProductReduce.reduceProducts column024Pairs) = true := by decide +kernel
#print axioms column024Checked
theorem column025Clearing_ne_zero : column025Clearing ≠ 0 := by decide +kernel
theorem column025Checked : zero (N6.SparseProductReduce.reduceProducts column025Pairs) = true := by decide +kernel
#print axioms column025Checked
theorem column026Clearing_ne_zero : column026Clearing ≠ 0 := by decide +kernel
theorem column026Checked : zero (N6.SparseProductReduce.reduceProducts column026Pairs) = true := by decide +kernel
#print axioms column026Checked
theorem column027Clearing_ne_zero : column027Clearing ≠ 0 := by decide +kernel
theorem column027Checked : zero (N6.SparseProductReduce.reduceProducts column027Pairs) = true := by decide +kernel
#print axioms column027Checked
theorem column028Clearing_ne_zero : column028Clearing ≠ 0 := by decide +kernel
theorem column028Checked : zero (N6.SparseProductReduce.reduceProducts column028Pairs) = true := by decide +kernel
#print axioms column028Checked
theorem column029Clearing_ne_zero : column029Clearing ≠ 0 := by decide +kernel
theorem column029Checked : zero (N6.SparseProductReduce.reduceProducts column029Pairs) = true := by decide +kernel
#print axioms column029Checked
theorem column030Clearing_ne_zero : column030Clearing ≠ 0 := by decide +kernel
theorem column030Checked : zero (N6.SparseProductReduce.reduceProducts column030Pairs) = true := by decide +kernel
#print axioms column030Checked
theorem column031Clearing_ne_zero : column031Clearing ≠ 0 := by decide +kernel
theorem column031Checked : zero (N6.SparseProductReduce.reduceProducts column031Pairs) = true := by decide +kernel
#print axioms column031Checked
end N6.Weighted49
