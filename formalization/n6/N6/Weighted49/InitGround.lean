import N6.Weighted49.InitData
import N6.SparseProductReduceCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem initClearing_nonzero : step136Left ≠ 0 := by decide +kernel
theorem initListChecked : scaleList step136Left vec_K000Data.toList = foldColumns 49 initWeightsData.toList initColumnsList := by decide +kernel
theorem initWeightsChecked : ∀ j : Fin 76, initWeights j * initDens j = step136Left * den_K000 * initCoefficients j := by decide +kernel
theorem initDChecked : zero (N6.SparseProductReduce.reduceProducts initDPairs) = true := by decide +kernel
#print axioms initListChecked
#print axioms initWeightsChecked
#print axioms initDChecked
end N6.Weighted49
