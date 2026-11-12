import N6.Weighted49.ActionData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem WA036Checked : zero (N6.SparseProductReduce.reduceProducts WA036Pairs) = true := by decide +kernel
#print axioms WA036Checked
theorem WA037Checked : zero (N6.SparseProductReduce.reduceProducts WA037Pairs) = true := by decide +kernel
#print axioms WA037Checked
theorem WA038Checked : zero (N6.SparseProductReduce.reduceProducts WA038Pairs) = true := by decide +kernel
#print axioms WA038Checked
theorem WA039Checked : zero (N6.SparseProductReduce.reduceProducts WA039Pairs) = true := by decide +kernel
#print axioms WA039Checked
end N6.Weighted49
