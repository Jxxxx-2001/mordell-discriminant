import N6.Exceptional.Bindings
import N6.Exceptional.ChartIVData
import review.SparseCheck
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.KroneckerCheck
theorem ChartIVR2_eval (e : ℂ) : value (point 0 0 1 e 0) C2 = value (point 0 0 1 e 0) ChartIVR2 := by
  norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, C2, C2Part0, C2Part1, ChartIVR2, ChartIVR2Part0] <;> ring
end N6.Exceptional
