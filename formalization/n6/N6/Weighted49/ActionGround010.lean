import N6.Weighted49.ActionData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem WA040Checked : zero (N6.SparseProductReduce.reduceProducts WA040Pairs) = true := by decide +kernel
#print axioms WA040Checked
theorem WA041Checked : zero (N6.SparseProductReduce.reduceProducts WA041Pairs) = true := by decide +kernel
#print axioms WA041Checked
theorem WA042Checked : zero (N6.SparseProductReduce.reduceProducts WA042Pairs) = true := by decide +kernel
#print axioms WA042Checked
theorem WA043Checked : zero (N6.SparseProductReduce.reduceProducts WA043Pairs) = true := by decide +kernel
#print axioms WA043Checked
end N6.Weighted49
