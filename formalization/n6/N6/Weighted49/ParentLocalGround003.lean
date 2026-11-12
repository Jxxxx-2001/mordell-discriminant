import N6.Weighted49.ParentLocalData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem D1Q034Checked : zero (N6.SparseProductReduce.reduceProducts D1Q034Pairs) = true := by decide +kernel
#print axioms D1Q034Checked
theorem D1Q035Checked : zero (N6.SparseProductReduce.reduceProducts D1Q035Pairs) = true := by decide +kernel
#print axioms D1Q035Checked
end N6.Weighted49
