import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column080Clearing_ne_zero : column080Clearing ≠ 0 := by decide +kernel
theorem column080Checked : zero (N6.SparseProductReduce.reduceProducts column080Pairs) = true := by decide +kernel
#print axioms column080Checked
theorem column081Clearing_ne_zero : column081Clearing ≠ 0 := by decide +kernel
theorem column081Checked : zero (N6.SparseProductReduce.reduceProducts column081Pairs) = true := by decide +kernel
#print axioms column081Checked
theorem column082Clearing_ne_zero : column082Clearing ≠ 0 := by decide +kernel
theorem column082Checked : zero (N6.SparseProductReduce.reduceProducts column082Pairs) = true := by decide +kernel
#print axioms column082Checked
theorem column083Clearing_ne_zero : column083Clearing ≠ 0 := by decide +kernel
theorem column083Checked : zero (N6.SparseProductReduce.reduceProducts column083Pairs) = true := by decide +kernel
#print axioms column083Checked
theorem column084Clearing_ne_zero : column084Clearing ≠ 0 := by decide +kernel
theorem column084Checked : zero (N6.SparseProductReduce.reduceProducts column084Pairs) = true := by decide +kernel
#print axioms column084Checked
theorem column085Clearing_ne_zero : column085Clearing ≠ 0 := by decide +kernel
theorem column085Checked : zero (N6.SparseProductReduce.reduceProducts column085Pairs) = true := by decide +kernel
#print axioms column085Checked
theorem column086Clearing_ne_zero : column086Clearing ≠ 0 := by decide +kernel
theorem column086Checked : zero (N6.SparseProductReduce.reduceProducts column086Pairs) = true := by decide +kernel
#print axioms column086Checked
theorem column087Clearing_ne_zero : column087Clearing ≠ 0 := by decide +kernel
theorem column087Checked : zero (N6.SparseProductReduce.reduceProducts column087Pairs) = true := by decide +kernel
#print axioms column087Checked
end N6.Weighted49
