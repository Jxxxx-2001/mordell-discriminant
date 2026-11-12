import N6.Even.ProgramSourceData
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
namespace N6.Even.ProgramData
open N6.SparseCheck N6.BranchEval.Program

theorem all_checked : checkBlock program 0 196 = true := by decide +kernel
#print axioms all_checked
theorem input0_den_ne_zero : input0NF.den ≠ 0 := by decide +kernel
theorem input1_den_ne_zero : input1NF.den ≠ 0 := by decide +kernel
theorem input2_den_ne_zero : input2NF.den ≠ 0 := by decide +kernel
theorem input3_den_ne_zero : input3NF.den ≠ 0 := by decide +kernel
theorem input4_den_ne_zero : input4NF.den ≠ 0 := by decide +kernel
theorem input5_den_ne_zero : input5NF.den ≠ 0 := by decide +kernel
theorem input6_den_ne_zero : input6NF.den ≠ 0 := by decide +kernel
theorem actualD_binding : matchesExpr program actualDExpr 60 = true := by decide +kernel
theorem actualR4_binding : matchesExpr program actualR4Expr 116 = true := by decide +kernel
theorem actualR02_binding : matchesExpr program actualR02Expr 176 = true := by decide +kernel
theorem DtimesAy_binding : matchesExpr program DtimesAyExpr 181 = true := by decide +kernel
theorem DtimesR02_binding : matchesExpr program DtimesR02Expr 182 = true := by decide +kernel
theorem ctimesR4sq_binding : matchesExpr program ctimesR4sqExpr 184 = true := by decide +kernel
theorem objectiveFormula_binding : matchesExpr program objectiveFormulaExpr 194 = true := by decide +kernel
theorem endpoint0_same_nf : (program.row 60).out = (program.row 177).out := by decide +kernel
theorem endpoint1_same_nf : (program.row 116).out = (program.row 178).out := by decide +kernel
theorem endpoint2_same_nf : (program.row 176).out = (program.row 179).out := by decide +kernel
theorem endpoint3_same_nf : (program.row 181).out = (program.row 178).out := by decide +kernel
theorem endpoint4_same_nf : (program.row 182).out = (program.row 184).out := by decide +kernel
theorem endpoint5_same_nf : (program.row 194).out = (program.row 195).out := by decide +kernel
end N6.Even.ProgramData
