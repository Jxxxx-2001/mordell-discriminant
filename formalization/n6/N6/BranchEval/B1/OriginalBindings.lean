import N6.BranchEval.B1.EndpointDefinitions
import N6.Chart
import N6.ResultantMinors.R4Semantics
import N6.Univariate.Soundness
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.BranchEval.B1.ProgramData
open N6.SparseCheck N6.KroneckerCheck N6.BranchEval.Program
variable {K : Type*} [Field K] [CharZero K]
theorem originalD_chart (b c k e : K) : originalD (b^2) c k e = N6.Chart.originalD b c (b*k) e := by unfold originalD N6.Chart.originalD; ring
theorem originalR4_quotient (B c k e : K) : originalR4 B c k e = value (N6.ResultantMinors.point B c k e 0) N6.ResultantMinors.quotientR4Data := by
  simp only [originalR4, N6.ResultantMinors.quotientR4DataPart0, N6.ResultantMinors.quotientR4DataPart1, N6.ResultantMinors.quotientR4DataPart2, N6.ResultantMinors.quotientR4DataPart3, N6.ResultantMinors.quotientR4DataPart4, N6.ResultantMinors.quotientR4Data, value_append, value, monVal, N6.ResultantMinors.point_eval0, N6.ResultantMinors.point_eval1, N6.ResultantMinors.point_eval2, N6.ResultantMinors.point_eval3, N6.ResultantMinors.point_eval4]
  ring
theorem originalR4_actual (b c k e : ℂ) : originalR4 (b^2) c k e = value (N6.ResultantMinors.point b c (b*k) e 0) (N6.ResultantMinors.extractY 4 N6.ResultantMinors.D063) := by
  rw [N6.ResultantMinors.rawR4_substitution]
  exact originalR4_quotient (b^2) c k e
#print axioms originalD_chart
#print axioms originalR4_actual
end N6.BranchEval.B1.ProgramData
