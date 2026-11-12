import N6.Weighted49.ActionData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem WA024Checked : zero (N6.SparseProductReduce.reduceProducts WA024Pairs) = true := by decide +kernel
#print axioms WA024Checked
theorem WA025Checked : zero (N6.SparseProductReduce.reduceProducts WA025Pairs) = true := by decide +kernel
#print axioms WA025Checked
theorem WA026Checked : zero (N6.SparseProductReduce.reduceProducts WA026Pairs) = true := by decide +kernel
#print axioms WA026Checked
theorem WA027Checked : zero (N6.SparseProductReduce.reduceProducts WA027Pairs) = true := by decide +kernel
#print axioms WA027Checked
end N6.Weighted49
