import N6.Weighted49.ActionData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem WA032Checked : zero (N6.SparseProductReduce.reduceProducts WA032Pairs) = true := by decide +kernel
#print axioms WA032Checked
theorem WA033Checked : zero (N6.SparseProductReduce.reduceProducts WA033Pairs) = true := by decide +kernel
#print axioms WA033Checked
theorem WA034Checked : zero (N6.SparseProductReduce.reduceProducts WA034Pairs) = true := by decide +kernel
#print axioms WA034Checked
theorem WA035Checked : zero (N6.SparseProductReduce.reduceProducts WA035Pairs) = true := by decide +kernel
#print axioms WA035Checked
end N6.Weighted49
