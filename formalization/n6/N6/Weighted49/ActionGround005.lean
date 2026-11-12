import N6.Weighted49.ActionData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem WA020Checked : zero (N6.SparseProductReduce.reduceProducts WA020Pairs) = true := by decide +kernel
#print axioms WA020Checked
theorem WA021Checked : zero (N6.SparseProductReduce.reduceProducts WA021Pairs) = true := by decide +kernel
#print axioms WA021Checked
theorem WA022Checked : zero (N6.SparseProductReduce.reduceProducts WA022Pairs) = true := by decide +kernel
#print axioms WA022Checked
theorem WA023Checked : zero (N6.SparseProductReduce.reduceProducts WA023Pairs) = true := by decide +kernel
#print axioms WA023Checked
end N6.Weighted49
