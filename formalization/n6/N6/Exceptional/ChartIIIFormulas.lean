import N6.Exceptional.Bindings
import N6.Exceptional.ChartIIIData
import review.SparseCheck
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.KroneckerCheck
theorem ChartIIIE0_eval (d e : ℂ) : value (point 0 1 d e 0) L3 = value (point 0 1 d e 0) ChartIIIE0 := by
  norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, L3, L3Part0, L3Part1, ChartIIIE0, ChartIIIE0Part0] <;> ring
theorem ChartIIIE1_eval (d e : ℂ) : value (point 0 1 d e 0) L2 - 12 * value (point 0 1 d e 0) C4 = value (point 0 1 d e 0) ChartIIIE1 := by
  norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, L2, L2Part0, L2Part1, C4, C4Part0, C4Part1, ChartIIIE1, ChartIIIE1Part0] <;> ring
theorem ChartIIIE2_eval (d e : ℂ) : value (point 0 1 d e 0) L1 - 6 * value (point 0 1 d e 0) C3 = value (point 0 1 d e 0) ChartIIIE2 := by
  norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, L1, L1Part0, L1Part1, C3, C3Part0, C3Part1, ChartIIIE2, ChartIIIE2Part0] <;> ring
theorem ChartIIIE3_eval (d e : ℂ) : value (point 0 1 d e 0) L0 - 2 * value (point 0 1 d e 0) C2 = value (point 0 1 d e 0) ChartIIIE3 := by
  norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, L0, L0Part0, C2, C2Part0, C2Part1, ChartIIIE3, ChartIIIE3Part0] <;> ring
theorem ChartIIIR4_eval (d e : ℂ) : value (point 0 1 d e 0) C4 = value (point 0 1 d e 0) ChartIIIR4 := by
  norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, C4, C4Part0, C4Part1, ChartIIIR4, ChartIIIR4Part0] <;> ring
theorem ChartIIIR3_eval (d e : ℂ) : value (point 0 1 d e 0) C3 = value (point 0 1 d e 0) ChartIIIR3 := by
  norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, C3, C3Part0, C3Part1, ChartIIIR3, ChartIIIR3Part0] <;> ring
theorem ChartIIIDelta_eval (d e : ℂ) : value (point 0 1 d e 0) C6 = value (point 0 1 d e 0) ChartIIIDelta := by
  norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, C6, C6Part0, C6Part1, ChartIIIDelta, ChartIIIDeltaPart0] <;> ring
end N6.Exceptional
