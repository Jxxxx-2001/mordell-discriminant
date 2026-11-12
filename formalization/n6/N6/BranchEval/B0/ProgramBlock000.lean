import N6.BranchEval.B0.ProgramData
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.BranchEval.B0.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
theorem block000_checked : checkBlock program 0 16 = true := by decide +kernel
#print axioms block000_checked
end N6.BranchEval.B0.ProgramData
