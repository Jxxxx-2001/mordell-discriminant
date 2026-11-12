import N6.ExceptionalA1.Bindings
import N6.Certificate
import Mathlib.Tactic.NormNum
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.ExceptionalA1
open N6.SparseCheck N6.KroneckerCheck
variable {K : Type*} [Field K] [CharZero K]
theorem impossible_values (x : Fin 5 → K) (t : K)
    (h0 : value x eq0 = 0)
    (h1 : value x eq1 = 0)
    (h2 : value x eq2 = 0)
    (h3 : value x eq3 = 0)
    (h4 : value x eq4 = 0)
    (hs : t*x 2*value x delta - 1 = 0) : False := by
  have h := certificate_identity x
  simp only [certificatePairs, N6.KroneckerCheck.pairs, goalFactor_value, h0, h1, h2, h3, h4, mul_zero, add_zero] at h
  have hz : (x 2)^3*value x delta = 0 := by
    apply N6.Certificate.int_scaled_zero clearing clearing_nonzero
    linear_combination h
  have hd : x 2 ≠ 0 := by intro hd; rw [hd] at hs; norm_num at hs
  have hD : value x delta ≠ 0 := by intro hD; rw [hD] at hs; norm_num at hs
  exact (mul_ne_zero (pow_ne_zero 3 hd) hD) hz
theorem impossible (c d e t : K)
    (h0 : N6.Chart.E0 0 c d e = 0)
    (h1 : N6.Chart.E1 0 c d e = 0)
    (h2 : N6.Chart.E2 0 c d e = 0)
    (h3 : N6.Chart.E3 0 c d e = 0)
    (hR03 : value (N6.ResultantMinors.point 0 c d e 0) (N6.ResultantMinors.extractY 3 N6.ResultantMinors.D063) = 0)
    (hs : t*d*N6.Chart.originalD 0 c d e - 1 = 0) : False := by
  apply impossible_values (N6.ResultantMinors.point 0 c d e 0) t
  · simpa only [eq0_actual] using h0
  · simpa only [eq1_actual] using h1
  · simpa only [eq2_actual] using h2
  · simpa only [eq3_actual] using h3
  · simpa only [eq4_actual] using hR03
  · simpa only [N6.ResultantMinors.point_eval2, delta_actual] using hs
#print axioms impossible_values
#print axioms impossible
end N6.ExceptionalA1
