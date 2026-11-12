import N6.Exceptional.Bindings
import N6.Exceptional.ChartIIData
import review.SparseCheck
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.KroneckerCheck
theorem ChartIIE0_eval (c d e : ℂ) : value (point 1 c d e 0) L3 = value (point 1 c d e 0) ChartIIE0 := by
  norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, L3, L3Part0, L3Part1, ChartIIE0, ChartIIE0Part0, ChartIIE0Part1] <;> ring
theorem ChartIIE1_eval (c d e : ℂ) : value (point 1 c d e 0) L2 - 12 * value (point 1 c d e 0) C4 = value (point 1 c d e 0) ChartIIE1 := by
  norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, L2, L2Part0, L2Part1, C4, C4Part0, C4Part1, ChartIIE1, ChartIIE1Part0, ChartIIE1Part1] <;> ring
theorem ChartIIE2_eval (c d e : ℂ) : value (point 1 c d e 0) L1 - 6 * value (point 1 c d e 0) C3 = value (point 1 c d e 0) ChartIIE2 := by
  norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, L1, L1Part0, L1Part1, C3, C3Part0, C3Part1, ChartIIE2, ChartIIE2Part0, ChartIIE2Part1] <;> ring
theorem ChartIIE3_eval (c d e : ℂ) : value (point 1 c d e 0) L0 - 2 * value (point 1 c d e 0) C2 = value (point 1 c d e 0) ChartIIE3 := by
  norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, L0, L0Part0, C2, C2Part0, C2Part1, ChartIIE3, ChartIIE3Part0, ChartIIE3Part1] <;> ring
theorem ChartIIR4_eval (c d e : ℂ) : value (point 1 c d e 0) C4 = value (point 1 c d e 0) ChartIIR4 := by
  norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, C4, C4Part0, C4Part1, ChartIIR4, ChartIIR4Part0, ChartIIR4Part1] <;> ring
theorem ChartIIDelta_eval (c d e : ℂ) : value (point 1 c d e 0) C6 = value (point 1 c d e 0) ChartIIDelta := by
  norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, C6, C6Part0, C6Part1, ChartIIDelta, ChartIIDeltaPart0, ChartIIDeltaPart1] <;> ring
end N6.Exceptional
