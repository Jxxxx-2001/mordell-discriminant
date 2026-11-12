import N6.BranchEval.B0.ProgramSourceData

set_option maxRecDepth 64000
set_option maxHeartbeats 6000000

namespace N6.BranchEval.B0.ProgramData
open N6.SparseCheck N6.BranchEval.Program

theorem originalD_binding : matchesExpr program originalDExpr 405 = true := by decide +kernel
#print axioms originalD_binding

theorem originalR4_binding : matchesExpr program originalR4Expr 795 = true := by decide +kernel
#print axioms originalR4_binding

theorem HofAy_binding : matchesExpr program HofAyExpr 805 = true := by decide +kernel
#print axioms HofAy_binding

theorem BofAy_binding : matchesExpr program BofAyExpr 807 = true := by decide +kernel
#print axioms BofAy_binding

theorem VofAy_binding : matchesExpr program VofAyExpr 809 = true := by decide +kernel
#print axioms VofAy_binding

theorem physicalSquare_binding : matchesExpr program physicalSquareExpr 819 = true := by decide +kernel
#print axioms physicalSquare_binding

theorem DiTimesAy_binding : matchesExpr program DiTimesAyExpr 798 = true := by decide +kernel
#print axioms DiTimesAy_binding

theorem endpoint00_same_nf : (program.row 405).out = (program.row 406).out := by decide +kernel
#print axioms endpoint00_same_nf

theorem endpoint01_same_nf : (program.row 795).out = (program.row 796).out := by decide +kernel
#print axioms endpoint01_same_nf

theorem endpoint02_same_nf : (program.row 798).out = (program.row 796).out := by decide +kernel
#print axioms endpoint02_same_nf

theorem endpoint03_same_nf : (program.row 805).out = (program.row 799).out := by decide +kernel
#print axioms endpoint03_same_nf

theorem endpoint04_same_nf : (program.row 807).out = (program.row 0).out := by decide +kernel
#print axioms endpoint04_same_nf

theorem endpoint05_same_nf : (program.row 809).out = (program.row 819).out := by decide +kernel
#print axioms endpoint05_same_nf

end N6.BranchEval.B0.ProgramData
