import N6.Exceptional.Data
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.SparseProductReduce
theorem constChecked045 : zero (reduceProducts constPairs045) = true := by decide +kernel
#print axioms constChecked045
theorem linearChecked045 : zero (reduceProducts linearPairs045) = true := by decide +kernel
#print axioms linearChecked045
theorem constChecked046 : zero (reduceProducts constPairs046) = true := by decide +kernel
#print axioms constChecked046
theorem linearChecked046 : zero (reduceProducts linearPairs046) = true := by decide +kernel
#print axioms linearChecked046
theorem constChecked051 : zero (reduceProducts constPairs051) = true := by decide +kernel
#print axioms constChecked051
theorem linearChecked051 : zero (reduceProducts linearPairs051) = true := by decide +kernel
#print axioms linearChecked051
theorem constChecked053 : zero (reduceProducts constPairs053) = true := by decide +kernel
#print axioms constChecked053
theorem linearChecked053 : zero (reduceProducts linearPairs053) = true := by decide +kernel
#print axioms linearChecked053
theorem constChecked054 : zero (reduceProducts constPairs054) = true := by decide +kernel
#print axioms constChecked054
theorem linearChecked054 : zero (reduceProducts linearPairs054) = true := by decide +kernel
#print axioms linearChecked054
theorem constChecked057 : zero (reduceProducts constPairs057) = true := by decide +kernel
#print axioms constChecked057
theorem linearChecked057 : zero (reduceProducts linearPairs057) = true := by decide +kernel
#print axioms linearChecked057
theorem constChecked058 : zero (reduceProducts constPairs058) = true := by decide +kernel
#print axioms constChecked058
theorem linearChecked058 : zero (reduceProducts linearPairs058) = true := by decide +kernel
#print axioms linearChecked058
theorem constChecked060 : zero (reduceProducts constPairs060) = true := by decide +kernel
#print axioms constChecked060
theorem linearChecked060 : zero (reduceProducts linearPairs060) = true := by decide +kernel
#print axioms linearChecked060
end N6.Exceptional
