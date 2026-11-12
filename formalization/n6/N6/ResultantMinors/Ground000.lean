import N6.ResultantMinors.Data
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.SparseProductReduce
theorem constChecked001 : zero (reduceProducts constPairs001) = true := by decide +kernel
#print axioms constChecked001
theorem linearChecked001 : zero (reduceProducts linearPairs001) = true := by decide +kernel
#print axioms linearChecked001
theorem constChecked002 : zero (reduceProducts constPairs002) = true := by decide +kernel
#print axioms constChecked002
theorem linearChecked002 : zero (reduceProducts linearPairs002) = true := by decide +kernel
#print axioms linearChecked002
theorem constChecked004 : zero (reduceProducts constPairs004) = true := by decide +kernel
#print axioms constChecked004
theorem linearChecked004 : zero (reduceProducts linearPairs004) = true := by decide +kernel
#print axioms linearChecked004
theorem constChecked008 : zero (reduceProducts constPairs008) = true := by decide +kernel
#print axioms constChecked008
theorem linearChecked008 : zero (reduceProducts linearPairs008) = true := by decide +kernel
#print axioms linearChecked008
theorem constChecked016 : zero (reduceProducts constPairs016) = true := by decide +kernel
#print axioms constChecked016
theorem linearChecked016 : zero (reduceProducts linearPairs016) = true := by decide +kernel
#print axioms linearChecked016
theorem constChecked032 : zero (reduceProducts constPairs032) = true := by decide +kernel
#print axioms constChecked032
theorem linearChecked032 : zero (reduceProducts linearPairs032) = true := by decide +kernel
#print axioms linearChecked032
theorem constChecked003 : zero (reduceProducts constPairs003) = true := by decide +kernel
#print axioms constChecked003
theorem linearChecked003 : zero (reduceProducts linearPairs003) = true := by decide +kernel
#print axioms linearChecked003
theorem constChecked005 : zero (reduceProducts constPairs005) = true := by decide +kernel
#print axioms constChecked005
theorem linearChecked005 : zero (reduceProducts linearPairs005) = true := by decide +kernel
#print axioms linearChecked005
end N6.ResultantMinors
