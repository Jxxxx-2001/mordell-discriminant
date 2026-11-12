import N6.Weighted49.ParentLocalData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem D1Q022Checked : zero (N6.SparseProductReduce.reduceProducts D1Q022Pairs) = true := by decide +kernel
#print axioms D1Q022Checked
theorem D1Q023Checked : zero (N6.SparseProductReduce.reduceProducts D1Q023Pairs) = true := by decide +kernel
#print axioms D1Q023Checked
theorem D1Q024Checked : zero (N6.SparseProductReduce.reduceProducts D1Q024Pairs) = true := by decide +kernel
#print axioms D1Q024Checked
theorem D1Q025Checked : zero (N6.SparseProductReduce.reduceProducts D1Q025Pairs) = true := by decide +kernel
#print axioms D1Q025Checked
end N6.Weighted49
