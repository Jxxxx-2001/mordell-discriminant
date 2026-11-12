import N6.Exceptional.Data
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.SparseProductReduce
theorem constChecked033 : zero (reduceProducts constPairs033) = true := by decide +kernel
#print axioms constChecked033
theorem linearChecked033 : zero (reduceProducts linearPairs033) = true := by decide +kernel
#print axioms linearChecked033
theorem constChecked034 : zero (reduceProducts constPairs034) = true := by decide +kernel
#print axioms constChecked034
theorem linearChecked034 : zero (reduceProducts linearPairs034) = true := by decide +kernel
#print axioms linearChecked034
theorem constChecked036 : zero (reduceProducts constPairs036) = true := by decide +kernel
#print axioms constChecked036
theorem linearChecked036 : zero (reduceProducts linearPairs036) = true := by decide +kernel
#print axioms linearChecked036
theorem constChecked040 : zero (reduceProducts constPairs040) = true := by decide +kernel
#print axioms constChecked040
theorem linearChecked040 : zero (reduceProducts linearPairs040) = true := by decide +kernel
#print axioms linearChecked040
theorem constChecked048 : zero (reduceProducts constPairs048) = true := by decide +kernel
#print axioms constChecked048
theorem linearChecked048 : zero (reduceProducts linearPairs048) = true := by decide +kernel
#print axioms linearChecked048
theorem constChecked007 : zero (reduceProducts constPairs007) = true := by decide +kernel
#print axioms constChecked007
theorem linearChecked007 : zero (reduceProducts linearPairs007) = true := by decide +kernel
#print axioms linearChecked007
theorem constChecked011 : zero (reduceProducts constPairs011) = true := by decide +kernel
#print axioms constChecked011
theorem linearChecked011 : zero (reduceProducts linearPairs011) = true := by decide +kernel
#print axioms linearChecked011
theorem constChecked013 : zero (reduceProducts constPairs013) = true := by decide +kernel
#print axioms constChecked013
theorem linearChecked013 : zero (reduceProducts linearPairs013) = true := by decide +kernel
#print axioms linearChecked013
end N6.Exceptional
