import N6.BranchEval.B3.ProjectionData
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.BranchEval.B3.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
theorem projection_cL_nonzero : projection_cL ≠ 0 := by decide +kernel
theorem projection_cA_nonzero : N6.Weighted49.lex_cA ≠ 0 := by decide +kernel
theorem projection_cChecked : zero (N6.SparseProductReduce.reduceProducts projection_cPairs) = true := by decide +kernel
#print axioms projection_cChecked
theorem projection_kL_nonzero : projection_kL ≠ 0 := by decide +kernel
theorem projection_kA_nonzero : N6.Weighted49.lex_kA ≠ 0 := by decide +kernel
theorem projection_kChecked : zero (N6.SparseProductReduce.reduceProducts projection_kPairs) = true := by decide +kernel
#print axioms projection_kChecked
theorem projection_eL_nonzero : projection_eL ≠ 0 := by decide +kernel
theorem projection_eA_nonzero : N6.Weighted49.lex_eA ≠ 0 := by decide +kernel
theorem projection_eChecked : zero (N6.SparseProductReduce.reduceProducts projection_ePairs) = true := by decide +kernel
#print axioms projection_eChecked
end N6.BranchEval.B3.ProgramData
