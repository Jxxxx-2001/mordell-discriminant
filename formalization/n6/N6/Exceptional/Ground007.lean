import N6.Exceptional.Data
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.SparseProductReduce
theorem constChecked031 : zero (reduceProducts constPairs031) = true := by decide +kernel
#print axioms constChecked031
theorem linearChecked031 : zero (reduceProducts linearPairs031) = true := by decide +kernel
#print axioms linearChecked031
theorem constChecked047 : zero (reduceProducts constPairs047) = true := by decide +kernel
#print axioms constChecked047
theorem linearChecked047 : zero (reduceProducts linearPairs047) = true := by decide +kernel
#print axioms linearChecked047
theorem constChecked055 : zero (reduceProducts constPairs055) = true := by decide +kernel
#print axioms constChecked055
theorem linearChecked055 : zero (reduceProducts linearPairs055) = true := by decide +kernel
#print axioms linearChecked055
theorem constChecked059 : zero (reduceProducts constPairs059) = true := by decide +kernel
#print axioms constChecked059
theorem linearChecked059 : zero (reduceProducts linearPairs059) = true := by decide +kernel
#print axioms linearChecked059
theorem constChecked061 : zero (reduceProducts constPairs061) = true := by decide +kernel
#print axioms constChecked061
theorem linearChecked061 : zero (reduceProducts linearPairs061) = true := by decide +kernel
#print axioms linearChecked061
theorem constChecked062 : zero (reduceProducts constPairs062) = true := by decide +kernel
#print axioms constChecked062
theorem linearChecked062 : zero (reduceProducts linearPairs062) = true := by decide +kernel
#print axioms linearChecked062
theorem constChecked063 : zero (reduceProducts constPairs063) = true := by decide +kernel
#print axioms constChecked063
theorem linearChecked063 : zero (reduceProducts linearPairs063) = true := by decide +kernel
#print axioms linearChecked063
end N6.Exceptional
