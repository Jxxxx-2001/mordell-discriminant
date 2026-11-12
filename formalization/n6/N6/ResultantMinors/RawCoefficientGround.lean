import N6.ResultantMinors.RawCoefficientData
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
namespace N6.ResultantMinors
open N6.SparseCheck
theorem rawDChecked : zero rawDResidual = true := by decide +kernel
#print axioms rawDChecked
theorem rawE0Checked : zero rawE0Residual = true := by decide +kernel
#print axioms rawE0Checked
theorem rawE1Checked : zero rawE1Residual = true := by decide +kernel
#print axioms rawE1Checked
theorem rawE2Checked : zero rawE2Residual = true := by decide +kernel
#print axioms rawE2Checked
theorem rawE3Checked : zero rawE3Residual = true := by decide +kernel
#print axioms rawE3Checked
end N6.ResultantMinors
