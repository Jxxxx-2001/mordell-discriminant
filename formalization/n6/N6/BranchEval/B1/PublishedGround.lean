import N6.BranchEval.B1.PublishedData
import N6.BranchEval.B1.ProgramSourceData
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.BranchEval.B1.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
theorem zero_binding : matchesExpr program (.lit 0 1) 799 = true := by decide +kernel
theorem input0_den_ne_zero : input0NF.den ≠ 0 := by decide +kernel
theorem input1_den_ne_zero : input1NF.den ≠ 0 := by decide +kernel
theorem input2_den_ne_zero : input2NF.den ≠ 0 := by decide +kernel
theorem input3_den_ne_zero : input3NF.den ≠ 0 := by decide +kernel
theorem input4_den_ne_zero : input4NF.den ≠ 0 := by decide +kernel
theorem input5_den_ne_zero : input5NF.den ≠ 0 := by decide +kernel
theorem input6_den_ne_zero : input6NF.den ≠ 0 := by decide +kernel
end N6.BranchEval.B1.ProgramData
