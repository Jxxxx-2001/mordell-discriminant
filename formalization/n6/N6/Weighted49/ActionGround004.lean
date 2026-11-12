import N6.Weighted49.ActionData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem WA016Checked : zero (N6.SparseProductReduce.reduceProducts WA016Pairs) = true := by decide +kernel
#print axioms WA016Checked
theorem WA017Checked : zero (N6.SparseProductReduce.reduceProducts WA017Pairs) = true := by decide +kernel
#print axioms WA017Checked
theorem WA018Checked : zero (N6.SparseProductReduce.reduceProducts WA018Pairs) = true := by decide +kernel
#print axioms WA018Checked
theorem WA019Checked : zero (N6.SparseProductReduce.reduceProducts WA019Pairs) = true := by decide +kernel
#print axioms WA019Checked
end N6.Weighted49
