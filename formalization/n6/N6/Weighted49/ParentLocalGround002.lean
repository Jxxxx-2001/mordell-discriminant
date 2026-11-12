import N6.Weighted49.ParentLocalData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem D1Q030Checked : zero (N6.SparseProductReduce.reduceProducts D1Q030Pairs) = true := by decide +kernel
#print axioms D1Q030Checked
theorem D1Q031Checked : zero (N6.SparseProductReduce.reduceProducts D1Q031Pairs) = true := by decide +kernel
#print axioms D1Q031Checked
theorem D1Q032Checked : zero (N6.SparseProductReduce.reduceProducts D1Q032Pairs) = true := by decide +kernel
#print axioms D1Q032Checked
theorem D1Q033Checked : zero (N6.SparseProductReduce.reduceProducts D1Q033Pairs) = true := by decide +kernel
#print axioms D1Q033Checked
end N6.Weighted49
