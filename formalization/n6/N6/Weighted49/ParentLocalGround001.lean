import N6.Weighted49.ParentLocalData
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem D1Q026Checked : zero (N6.SparseProductReduce.reduceProducts D1Q026Pairs) = true := by decide +kernel
#print axioms D1Q026Checked
theorem D1Q027Checked : zero (N6.SparseProductReduce.reduceProducts D1Q027Pairs) = true := by decide +kernel
#print axioms D1Q027Checked
theorem D1Q028Checked : zero (N6.SparseProductReduce.reduceProducts D1Q028Pairs) = true := by decide +kernel
#print axioms D1Q028Checked
theorem D1Q029Checked : zero (N6.SparseProductReduce.reduceProducts D1Q029Pairs) = true := by decide +kernel
#print axioms D1Q029Checked
end N6.Weighted49
