import N6.Even.CoverageData

set_option maxRecDepth 32000
set_option maxHeartbeats 3000000

namespace N6.Even
open N6.SparseCheck N6.KroneckerCheck

theorem EvenFChecked : zero (N6.SparseProductReduce.reduceProducts EvenFPairs) = true := by decide +kernel
#print axioms EvenFChecked

theorem EvenGChecked : zero (N6.SparseProductReduce.reduceProducts EvenGPairs) = true := by decide +kernel
#print axioms EvenGChecked

theorem EvenP6Checked : zero (N6.SparseProductReduce.reduceProducts EvenP6Pairs) = true := by decide +kernel
#print axioms EvenP6Checked

theorem EvenEGraphChecked : zero (N6.SparseProductReduce.reduceProducts EvenEGraphPairs) = true := by decide +kernel
#print axioms EvenEGraphChecked

end N6.Even
