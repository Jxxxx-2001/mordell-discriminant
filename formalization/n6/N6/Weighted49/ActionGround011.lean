import N6.Weighted49.ActionData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem WA044Checked : zero (N6.SparseProductReduce.reduceProducts WA044Pairs) = true := by decide +kernel
#print axioms WA044Checked
theorem WA045Checked : zero (N6.SparseProductReduce.reduceProducts WA045Pairs) = true := by decide +kernel
#print axioms WA045Checked
theorem WA046Checked : zero (N6.SparseProductReduce.reduceProducts WA046Pairs) = true := by decide +kernel
#print axioms WA046Checked
theorem WA047Checked : zero (N6.SparseProductReduce.reduceProducts WA047Pairs) = true := by decide +kernel
#print axioms WA047Checked
end N6.Weighted49
