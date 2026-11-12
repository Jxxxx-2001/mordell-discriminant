import N6.BranchEval.B4.PublishedData
import N6.Univariate.Branch4Data
import N6.BranchEval.B4.ProgramSourceData
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.BranchEval.B4.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
theorem H_published : hCoefficients = N6.Univariate.Branch4.p := by decide +kernel
#print axioms H_published
theorem V_published : vCoefficients = N6.Univariate.Branch4.v := by decide +kernel
#print axioms V_published
theorem zero_binding : matchesExpr program (.lit 0 1) 799 = true := by decide +kernel
theorem input0_den_ne_zero : input0NF.den ≠ 0 := by decide +kernel
theorem input1_den_ne_zero : input1NF.den ≠ 0 := by decide +kernel
theorem input2_den_ne_zero : input2NF.den ≠ 0 := by decide +kernel
theorem input3_den_ne_zero : input3NF.den ≠ 0 := by decide +kernel
theorem input4_den_ne_zero : input4NF.den ≠ 0 := by decide +kernel
theorem input5_den_ne_zero : input5NF.den ≠ 0 := by decide +kernel
theorem input6_den_ne_zero : input6NF.den ≠ 0 := by decide +kernel
end N6.BranchEval.B4.ProgramData
