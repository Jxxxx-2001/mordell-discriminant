import N6.Exceptional.PolynomialBridge
import N6.Exceptional.ChartIVFormulas
import N6.Analysis.PhysicalCoefficients
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.KroneckerCheck
theorem ChartIV_of_scaled_maximum {z : N6.Configuration} (hz : N6.IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) (e : ℂ)
    (hp : N6.rootPolynomial (N6.scaleConfiguration α z) = N6.coefficientSextic 0 0 0 1 e) : e = 0 := by
  let w := N6.scaleConfiguration α z
  let y := N6.dualConfiguration w
  have sta := N6.scaled_dualStationaryPair hz hα
  have r0 := stationaryR0_eq_liftY sta 0 0 1 e hp
  have ph2 := N6.physical_resultant_zero_coefficient w y _ (N6.scaled_dual_physical hz hα) 2 (by
    change (N6.rootPolynomial (N6.scaleConfiguration α z)).coeff _ = 0
    rw [hp]; simp [N6.coefficientSextic, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow, Polynomial.coeff_X])
  dsimp only [w, y] at ph2
  simp only [r0, N6.ResultantMinors.coeff_liftY, projC2] at ph2
  have eq0 : value (point 0 0 1 e 0) ChartIVR2 = 0 := (ChartIVR2_eval e).symm.trans ph2
  have hx : value (point 0 0 1 e 0) ChartIVR2 = (8100000 : ℂ) * e := by
    norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, ChartIVR2, ChartIVR2Part0] <;> ring
  rw [hx] at eq0
  exact (mul_eq_zero.mp eq0).resolve_left (by norm_num)
#print axioms ChartIV_of_scaled_maximum
end N6.Exceptional
