import N6.ExceptionalA1.CertificateData
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.ExceptionalA1
open N6.SparseCheck N6.KroneckerCheck
theorem clearing_nonzero : clearing ≠ 0 := by decide +kernel
theorem certificateRoom : roomCheck certificateRad certificatePairs = true := by decide +kernel
#print axioms certificateRoom
theorem certificateMass : N6.KroneckerCheck.pairs mass certificatePairs < ((2 : Int)^certificateBits).natAbs := by decide +kernel
#print axioms certificateMass
theorem certificateFast : N6.KroneckerCheck.pairs (N6.KroneckerFastPack.fastPack certificateRad certificateBits certificateDepth) certificatePairs = 0 := by decide +kernel
#print axioms certificateFast
theorem deltaProjection : zero (merge (atBZero N6.ResultantMinors.rawDData) (scaled (-1) delta)) = true := by decide +kernel
#print axioms deltaProjection
theorem eq0Projection : zero (merge (atBZero N6.ResultantMinors.rawE0Data) (scaled (-1) eq0)) = true := by decide +kernel
#print axioms eq0Projection
theorem eq1Projection : zero (merge (atBZero N6.ResultantMinors.rawE1Data) (scaled (-1) eq1)) = true := by decide +kernel
#print axioms eq1Projection
theorem eq2Projection : zero (merge (atBZero N6.ResultantMinors.rawE2Data) (scaled (-1) eq2)) = true := by decide +kernel
#print axioms eq2Projection
theorem eq3Projection : zero (merge (atBZero N6.ResultantMinors.rawE3Data) (scaled (-1) eq3)) = true := by decide +kernel
#print axioms eq3Projection
theorem eq4Projection : zero (merge (atBZero (N6.ResultantMinors.extractY 3 N6.ResultantMinors.D063)) (scaled (-1) eq4)) = true := by decide +kernel
#print axioms eq4Projection
end N6.ExceptionalA1
