import N6.Exceptional.Data
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.SparseProductReduce
theorem constChecked014 : zero (reduceProducts constPairs014) = true := by decide +kernel
#print axioms constChecked014
theorem linearChecked014 : zero (reduceProducts linearPairs014) = true := by decide +kernel
#print axioms linearChecked014
theorem constChecked019 : zero (reduceProducts constPairs019) = true := by decide +kernel
#print axioms constChecked019
theorem linearChecked019 : zero (reduceProducts linearPairs019) = true := by decide +kernel
#print axioms linearChecked019
theorem constChecked021 : zero (reduceProducts constPairs021) = true := by decide +kernel
#print axioms constChecked021
theorem linearChecked021 : zero (reduceProducts linearPairs021) = true := by decide +kernel
#print axioms linearChecked021
theorem constChecked022 : zero (reduceProducts constPairs022) = true := by decide +kernel
#print axioms constChecked022
theorem linearChecked022 : zero (reduceProducts linearPairs022) = true := by decide +kernel
#print axioms linearChecked022
theorem constChecked025 : zero (reduceProducts constPairs025) = true := by decide +kernel
#print axioms constChecked025
theorem linearChecked025 : zero (reduceProducts linearPairs025) = true := by decide +kernel
#print axioms linearChecked025
theorem constChecked026 : zero (reduceProducts constPairs026) = true := by decide +kernel
#print axioms constChecked026
theorem linearChecked026 : zero (reduceProducts linearPairs026) = true := by decide +kernel
#print axioms linearChecked026
theorem constChecked028 : zero (reduceProducts constPairs028) = true := by decide +kernel
#print axioms constChecked028
theorem linearChecked028 : zero (reduceProducts linearPairs028) = true := by decide +kernel
#print axioms linearChecked028
theorem constChecked035 : zero (reduceProducts constPairs035) = true := by decide +kernel
#print axioms constChecked035
theorem linearChecked035 : zero (reduceProducts linearPairs035) = true := by decide +kernel
#print axioms linearChecked035
end N6.Exceptional
