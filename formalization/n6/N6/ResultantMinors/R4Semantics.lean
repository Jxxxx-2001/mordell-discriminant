import N6.ResultantMinors.R4Ground
import N6.ResultantMinors.Bindings
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
namespace N6.ResultantMinors
open N6.SparseCheck
theorem rawR4_substitution (b c k e : ℂ) :
    value (point b c (b*k) e 0) (extractY 4 D063) =
      value (point (b^2) c k e 0) quotientR4Data := by
  rw [rawR4_projection]
  simp only [rawR4Data, rawR4DataPart0, rawR4DataPart1, rawR4DataPart2, rawR4DataPart3, rawR4DataPart4, quotientR4Data, quotientR4DataPart0, quotientR4DataPart1, quotientR4DataPart2, quotientR4DataPart3, quotientR4DataPart4, N6.SparseCheck.value_append, N6.SparseCheck.value, N6.SparseCheck.monVal, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4]
  ring
#print axioms rawR4_substitution
end N6.ResultantMinors
