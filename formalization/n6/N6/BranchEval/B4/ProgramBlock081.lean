import N6.BranchEval.B4.ProgramData
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.BranchEval.B4.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
theorem block081_checked : checkBlock program 1296 13 = true := by decide +kernel
#print axioms block081_checked
end N6.BranchEval.B4.ProgramData
