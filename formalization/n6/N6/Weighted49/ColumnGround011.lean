import N6.Weighted49.ColumnData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column088Clearing_ne_zero : column088Clearing ≠ 0 := by decide +kernel
theorem column088Checked : zero (N6.SparseProductReduce.reduceProducts column088Pairs) = true := by decide +kernel
#print axioms column088Checked
theorem column089Clearing_ne_zero : column089Clearing ≠ 0 := by decide +kernel
theorem column089Checked : zero (N6.SparseProductReduce.reduceProducts column089Pairs) = true := by decide +kernel
#print axioms column089Checked
theorem column090Clearing_ne_zero : column090Clearing ≠ 0 := by decide +kernel
theorem column090Checked : zero (N6.SparseProductReduce.reduceProducts column090Pairs) = true := by decide +kernel
#print axioms column090Checked
theorem column091Clearing_ne_zero : column091Clearing ≠ 0 := by decide +kernel
theorem column091Checked : zero (N6.SparseProductReduce.reduceProducts column091Pairs) = true := by decide +kernel
#print axioms column091Checked
theorem column092Clearing_ne_zero : column092Clearing ≠ 0 := by decide +kernel
theorem column092Checked : zero (N6.SparseProductReduce.reduceProducts column092Pairs) = true := by decide +kernel
#print axioms column092Checked
theorem column093Clearing_ne_zero : column093Clearing ≠ 0 := by decide +kernel
theorem column093Checked : zero (N6.SparseProductReduce.reduceProducts column093Pairs) = true := by decide +kernel
#print axioms column093Checked
theorem column094Clearing_ne_zero : column094Clearing ≠ 0 := by decide +kernel
theorem column094Checked : zero (N6.SparseProductReduce.reduceProducts column094Pairs) = true := by decide +kernel
#print axioms column094Checked
theorem column095Clearing_ne_zero : column095Clearing ≠ 0 := by decide +kernel
theorem column095Checked : zero (N6.SparseProductReduce.reduceProducts column095Pairs) = true := by decide +kernel
#print axioms column095Checked
end N6.Weighted49
