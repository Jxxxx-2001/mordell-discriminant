import N6.Weighted49.ActionData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem WA000Checked : zero (N6.SparseProductReduce.reduceProducts WA000Pairs) = true := by decide +kernel
#print axioms WA000Checked
theorem WA001Checked : zero (N6.SparseProductReduce.reduceProducts WA001Pairs) = true := by decide +kernel
#print axioms WA001Checked
theorem WA002Checked : zero (N6.SparseProductReduce.reduceProducts WA002Pairs) = true := by decide +kernel
#print axioms WA002Checked
theorem WA003Checked : zero (N6.SparseProductReduce.reduceProducts WA003Pairs) = true := by decide +kernel
#print axioms WA003Checked
end N6.Weighted49
