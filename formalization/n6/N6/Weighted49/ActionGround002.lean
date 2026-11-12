import N6.Weighted49.ActionData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem WA008Checked : zero (N6.SparseProductReduce.reduceProducts WA008Pairs) = true := by decide +kernel
#print axioms WA008Checked
theorem WA009Checked : zero (N6.SparseProductReduce.reduceProducts WA009Pairs) = true := by decide +kernel
#print axioms WA009Checked
theorem WA010Checked : zero (N6.SparseProductReduce.reduceProducts WA010Pairs) = true := by decide +kernel
#print axioms WA010Checked
theorem WA011Checked : zero (N6.SparseProductReduce.reduceProducts WA011Pairs) = true := by decide +kernel
#print axioms WA011Checked
end N6.Weighted49
