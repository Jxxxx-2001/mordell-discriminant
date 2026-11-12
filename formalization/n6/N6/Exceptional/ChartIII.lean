import N6.Exceptional.PolynomialBridge
import N6.Exceptional.ChartIIIFormulas
import N6.Exceptional.ChartIIICertificates
import N6.Analysis.PhysicalCoefficients
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.KroneckerCheck
private theorem ChartIIIUnit_vanish (d e : ℂ)
    (eq0 : value (point 0 1 d e 0) ChartIIIE0 = 0)
    (eq1 : value (point 0 1 d e 0) ChartIIIE1 = 0)
    (eq2 : value (point 0 1 d e 0) ChartIIIE2 = 0)
    (eq3 : value (point 0 1 d e 0) ChartIIIE3 = 0)
    (eq4 : value (point 0 1 d e 0) ChartIIIR4 = 0)
    (eq5 : value (point 0 1 d e 0) ChartIIIR3 = 0)
    (hd : value (point 0 1 d e 0) ChartIIIDelta ≠ 0) : False := by
  have hh := ChartIIIUnit_checked (point 0 1 d e 0)
  simp only [ChartIIIUnitPairs, N6.KroneckerCheck.pairs, eq0, eq1, eq2, eq3, eq4, eq5, mul_zero, zero_add, add_zero] at hh
  have hzero := (mul_eq_zero.mp hh).resolve_left hd
  have hg : value (point 0 1 d e 0) ChartIIIUnitGoal = (-66355200 : ℂ) * 1 := by
    norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, ChartIIIUnitGoal, ChartIIIUnitGoalPart0] <;> ring
  rw [hg] at hzero
  norm_num at hzero
theorem ChartIII_of_scaled_maximum {z : N6.Configuration} (hz : N6.IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) (d e : ℂ)
    (hp : N6.rootPolynomial (N6.scaleConfiguration α z) = N6.coefficientSextic 0 0 1 d e) : False := by
  let w := N6.scaleConfiguration α z
  let y := N6.dualConfiguration w
  have sta := N6.scaled_dualStationaryPair hz hα
  have r0 := stationaryR0_eq_liftY sta 0 1 d e hp
  have rt := stationaryRT_eq_liftY sta 0 1 d e hp
  obtain ⟨h0,h1,h2,h3⟩ := N6.scaled_maximum_rawStationaryEquations hz hα
  simp only [r0, rt, N6.ResultantMinors.coeff_liftY, projL3] at h0
  have eq0 : value (point 0 1 d e 0) ChartIIIE0 = 0 := (ChartIIIE0_eval d e).symm.trans h0
  simp only [r0, rt, N6.ResultantMinors.coeff_liftY, projL2, projC4] at h1
  have eq1 : value (point 0 1 d e 0) ChartIIIE1 = 0 := (ChartIIIE1_eval d e).symm.trans h1
  simp only [r0, rt, N6.ResultantMinors.coeff_liftY, projL1, projC3] at h2
  have eq2 : value (point 0 1 d e 0) ChartIIIE2 = 0 := (ChartIIIE2_eval d e).symm.trans h2
  simp only [r0, rt, N6.ResultantMinors.coeff_liftY, projL0, projC2] at h3
  have eq3 : value (point 0 1 d e 0) ChartIIIE3 = 0 := (ChartIIIE3_eval d e).symm.trans h3
  have ph4 := N6.physical_resultant_zero_coefficient w y _ (N6.scaled_dual_physical hz hα) 4 (by
    change (N6.rootPolynomial (N6.scaleConfiguration α z)).coeff _ = 0
    rw [hp]; simp [N6.coefficientSextic, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow])
  dsimp only [w, y] at ph4
  simp only [r0, rt, N6.ResultantMinors.coeff_liftY, projC4] at ph4
  have eq4 : value (point 0 1 d e 0) ChartIIIR4 = 0 := (ChartIIIR4_eval d e).symm.trans ph4
  have ph3 := N6.physical_resultant_zero_coefficient w y _ (N6.scaled_dual_physical hz hα) 3 (by
    change (N6.rootPolynomial (N6.scaleConfiguration α z)).coeff _ = 0
    rw [hp]; simp [N6.coefficientSextic, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow])
  dsimp only [w, y] at ph3
  simp only [r0, rt, N6.ResultantMinors.coeff_liftY, projC3] at ph3
  have eq5 : value (point 0 1 d e 0) ChartIIIR3 = 0 := (ChartIIIR3_eval d e).symm.trans ph3
  have de := discriminant_coeff_identity sta 0 1 d e hp
  rw [projC6] at de
  have dn : value (point 0 1 d e 0) ChartIIIDelta ≠ 0 := by
    rw [← ChartIIIDelta_eval, ← de]
    exact N6.complexDiscriminant_ne (N6.scaled_injective hz hα)
  exact ChartIIIUnit_vanish d e eq0 eq1 eq2 eq3 eq4 eq5 dn
#print axioms ChartIII_of_scaled_maximum
end N6.Exceptional
