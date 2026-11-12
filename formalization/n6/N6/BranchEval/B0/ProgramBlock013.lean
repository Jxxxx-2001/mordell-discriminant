import N6.BranchEval.B0.ProgramData
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.BranchEval.B0.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
theorem block013_checked : checkBlock program 208 16 = true := by decide +kernel
#print axioms block013_checked
end N6.BranchEval.B0.ProgramData
