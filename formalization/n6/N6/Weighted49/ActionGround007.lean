import N6.Weighted49.ActionData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem WA028Checked : zero (N6.SparseProductReduce.reduceProducts WA028Pairs) = true := by decide +kernel
#print axioms WA028Checked
theorem WA029Checked : zero (N6.SparseProductReduce.reduceProducts WA029Pairs) = true := by decide +kernel
#print axioms WA029Checked
theorem WA030Checked : zero (N6.SparseProductReduce.reduceProducts WA030Pairs) = true := by decide +kernel
#print axioms WA030Checked
theorem WA031Checked : zero (N6.SparseProductReduce.reduceProducts WA031Pairs) = true := by decide +kernel
#print axioms WA031Checked
end N6.Weighted49
