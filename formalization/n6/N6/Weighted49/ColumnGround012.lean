import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column096Clearing_ne_zero : column096Clearing ≠ 0 := by decide +kernel
theorem column096Checked : zero (N6.SparseProductReduce.reduceProducts column096Pairs) = true := by decide +kernel
#print axioms column096Checked
theorem column097Clearing_ne_zero : column097Clearing ≠ 0 := by decide +kernel
theorem column097Checked : zero (N6.SparseProductReduce.reduceProducts column097Pairs) = true := by decide +kernel
#print axioms column097Checked
theorem column098Clearing_ne_zero : column098Clearing ≠ 0 := by decide +kernel
theorem column098Checked : zero (N6.SparseProductReduce.reduceProducts column098Pairs) = true := by decide +kernel
#print axioms column098Checked
theorem column099Clearing_ne_zero : column099Clearing ≠ 0 := by decide +kernel
theorem column099Checked : zero (N6.SparseProductReduce.reduceProducts column099Pairs) = true := by decide +kernel
#print axioms column099Checked
theorem column100Clearing_ne_zero : column100Clearing ≠ 0 := by decide +kernel
theorem column100Checked : zero (N6.SparseProductReduce.reduceProducts column100Pairs) = true := by decide +kernel
#print axioms column100Checked
theorem column101Clearing_ne_zero : column101Clearing ≠ 0 := by decide +kernel
theorem column101Checked : zero (N6.SparseProductReduce.reduceProducts column101Pairs) = true := by decide +kernel
#print axioms column101Checked
theorem column102Clearing_ne_zero : column102Clearing ≠ 0 := by decide +kernel
theorem column102Checked : zero (N6.SparseProductReduce.reduceProducts column102Pairs) = true := by decide +kernel
#print axioms column102Checked
theorem column103Clearing_ne_zero : column103Clearing ≠ 0 := by decide +kernel
theorem column103Checked : zero (N6.SparseProductReduce.reduceProducts column103Pairs) = true := by decide +kernel
#print axioms column103Checked
end N6.Weighted49
