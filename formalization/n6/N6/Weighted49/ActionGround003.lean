import N6.Weighted49.ActionData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem WA012Checked : zero (N6.SparseProductReduce.reduceProducts WA012Pairs) = true := by decide +kernel
#print axioms WA012Checked
theorem WA013Checked : zero (N6.SparseProductReduce.reduceProducts WA013Pairs) = true := by decide +kernel
#print axioms WA013Checked
theorem WA014Checked : zero (N6.SparseProductReduce.reduceProducts WA014Pairs) = true := by decide +kernel
#print axioms WA014Checked
theorem WA015Checked : zero (N6.SparseProductReduce.reduceProducts WA015Pairs) = true := by decide +kernel
#print axioms WA015Checked
end N6.Weighted49
