import N6.Weighted49.ActionData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem WA048Checked : zero (N6.SparseProductReduce.reduceProducts WA048Pairs) = true := by decide +kernel
#print axioms WA048Checked
end N6.Weighted49
