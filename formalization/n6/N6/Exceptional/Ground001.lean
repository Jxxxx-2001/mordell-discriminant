import N6.Exceptional.Data
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.SparseProductReduce
theorem constChecked006 : zero (reduceProducts constPairs006) = true := by decide +kernel
#print axioms constChecked006
theorem linearChecked006 : zero (reduceProducts linearPairs006) = true := by decide +kernel
#print axioms linearChecked006
theorem constChecked009 : zero (reduceProducts constPairs009) = true := by decide +kernel
#print axioms constChecked009
theorem linearChecked009 : zero (reduceProducts linearPairs009) = true := by decide +kernel
#print axioms linearChecked009
theorem constChecked010 : zero (reduceProducts constPairs010) = true := by decide +kernel
#print axioms constChecked010
theorem linearChecked010 : zero (reduceProducts linearPairs010) = true := by decide +kernel
#print axioms linearChecked010
theorem constChecked012 : zero (reduceProducts constPairs012) = true := by decide +kernel
#print axioms constChecked012
theorem linearChecked012 : zero (reduceProducts linearPairs012) = true := by decide +kernel
#print axioms linearChecked012
theorem constChecked017 : zero (reduceProducts constPairs017) = true := by decide +kernel
#print axioms constChecked017
theorem linearChecked017 : zero (reduceProducts linearPairs017) = true := by decide +kernel
#print axioms linearChecked017
theorem constChecked018 : zero (reduceProducts constPairs018) = true := by decide +kernel
#print axioms constChecked018
theorem linearChecked018 : zero (reduceProducts linearPairs018) = true := by decide +kernel
#print axioms linearChecked018
theorem constChecked020 : zero (reduceProducts constPairs020) = true := by decide +kernel
#print axioms constChecked020
theorem linearChecked020 : zero (reduceProducts linearPairs020) = true := by decide +kernel
#print axioms linearChecked020
theorem constChecked024 : zero (reduceProducts constPairs024) = true := by decide +kernel
#print axioms constChecked024
theorem linearChecked024 : zero (reduceProducts linearPairs024) = true := by decide +kernel
#print axioms linearChecked024
end N6.Exceptional
