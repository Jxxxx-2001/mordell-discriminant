import N6.Weighted49.ActionData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem WA004Checked : zero (N6.SparseProductReduce.reduceProducts WA004Pairs) = true := by decide +kernel
#print axioms WA004Checked
theorem WA005Checked : zero (N6.SparseProductReduce.reduceProducts WA005Pairs) = true := by decide +kernel
#print axioms WA005Checked
theorem WA006Checked : zero (N6.SparseProductReduce.reduceProducts WA006Pairs) = true := by decide +kernel
#print axioms WA006Checked
theorem WA007Checked : zero (N6.SparseProductReduce.reduceProducts WA007Pairs) = true := by decide +kernel
#print axioms WA007Checked
end N6.Weighted49
