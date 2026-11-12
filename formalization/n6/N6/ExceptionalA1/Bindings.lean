import N6.ExceptionalA1.Helpers
import N6.ResultantMinors.RawCoefficientBindings
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.ExceptionalA1
open N6.SparseCheck N6.KroneckerCheck
variable {K : Type*} [Field K] [CharZero K]
theorem delta_actual (c d e : K) : value (N6.ResultantMinors.point 0 c d e 0) delta = N6.Chart.originalD 0 c d e := by
  exact (projection_value _ (N6.ResultantMinors.point_eval4 0 c d e 0) N6.ResultantMinors.rawDData delta deltaProjection).trans (N6.ResultantMinors.rawD_chart 0 c d e)
theorem eq0_actual (c d e : K) : value (N6.ResultantMinors.point 0 c d e 0) eq0 = N6.Chart.E0 0 c d e := by
  exact (projection_value _ (N6.ResultantMinors.point_eval4 0 c d e 0) N6.ResultantMinors.rawE0Data eq0 eq0Projection).trans (N6.ResultantMinors.rawE0_chart 0 c d e)
theorem eq1_actual (c d e : K) : value (N6.ResultantMinors.point 0 c d e 0) eq1 = N6.Chart.E1 0 c d e := by
  exact (projection_value _ (N6.ResultantMinors.point_eval4 0 c d e 0) N6.ResultantMinors.rawE1Data eq1 eq1Projection).trans (N6.ResultantMinors.rawE1_chart 0 c d e)
theorem eq2_actual (c d e : K) : value (N6.ResultantMinors.point 0 c d e 0) eq2 = N6.Chart.E2 0 c d e := by
  exact (projection_value _ (N6.ResultantMinors.point_eval4 0 c d e 0) N6.ResultantMinors.rawE2Data eq2 eq2Projection).trans (N6.ResultantMinors.rawE2_chart 0 c d e)
theorem eq3_actual (c d e : K) : value (N6.ResultantMinors.point 0 c d e 0) eq3 = N6.Chart.E3 0 c d e := by
  exact (projection_value _ (N6.ResultantMinors.point_eval4 0 c d e 0) N6.ResultantMinors.rawE3Data eq3 eq3Projection).trans (N6.ResultantMinors.rawE3_chart 0 c d e)
theorem eq4_actual (c d e : K) : value (N6.ResultantMinors.point 0 c d e 0) eq4 = value (N6.ResultantMinors.point 0 c d e 0) (N6.ResultantMinors.extractY 3 N6.ResultantMinors.D063) := by
  exact projection_value _ (N6.ResultantMinors.point_eval4 0 c d e 0) _ _ eq4Projection
end N6.ExceptionalA1
