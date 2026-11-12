import N6.Exceptional.PolynomialBridge
import N6.Exceptional.ChartIIFormulas
import N6.Exceptional.ChartIICertificates
import N6.Analysis.PhysicalCoefficients
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.KroneckerCheck
private theorem ChartIIC_vanish (c d e : ℂ)
    (eq0 : value (point 1 c d e 0) ChartIIE0 = 0)
    (eq1 : value (point 1 c d e 0) ChartIIE1 = 0)
    (eq2 : value (point 1 c d e 0) ChartIIE2 = 0)
    (eq3 : value (point 1 c d e 0) ChartIIE3 = 0)
    (eq4 : value (point 1 c d e 0) ChartIIR4 = 0)
    (hd : value (point 1 c d e 0) ChartIIDelta ≠ 0) : c = 0 := by
  have hh := ChartIIC_checked (point 1 c d e 0)
  simp only [ChartIICPairs, N6.KroneckerCheck.pairs, eq0, eq1, eq2, eq3, eq4, mul_zero, zero_add, add_zero] at hh
  have hzero := (mul_eq_zero.mp hh).resolve_left hd
  have hg : value (point 1 c d e 0) ChartIICGoal = (-32228878050142597783756506054419116606578098751377956798953871995926824870760632320000 : ℂ) * c := by
    norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, ChartIICGoal, ChartIICGoalPart0] <;> ring
  rw [hg] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
private theorem ChartIID_vanish (c d e : ℂ)
    (eq0 : value (point 1 c d e 0) ChartIIE0 = 0)
    (eq1 : value (point 1 c d e 0) ChartIIE1 = 0)
    (eq2 : value (point 1 c d e 0) ChartIIE2 = 0)
    (eq3 : value (point 1 c d e 0) ChartIIE3 = 0)
    (eq4 : value (point 1 c d e 0) ChartIIR4 = 0)
    (hd : value (point 1 c d e 0) ChartIIDelta ≠ 0) : d = 0 := by
  have hh := ChartIID_checked (point 1 c d e 0)
  simp only [ChartIIDPairs, N6.KroneckerCheck.pairs, eq0, eq1, eq2, eq3, eq4, mul_zero, zero_add, add_zero] at hh
  have hzero := (mul_eq_zero.mp hh).resolve_left hd
  have hg : value (point 1 c d e 0) ChartIIDGoal = (-29286582214218688478712826196100028297270696716087399618255368486835432873179515312025329601972826640470837582812463799391608084698476754861293189049551461109167381395456000000 : ℂ) * d := by
    norm_num [value, monVal, value_append, point_eval0, point_eval1, point_eval2, point_eval3, point_eval4, ChartIIDGoal, ChartIIDGoalPart0] <;> ring
  rw [hg] at hzero
  exact (mul_eq_zero.mp hzero).resolve_left (by norm_num)
theorem ChartII_of_scaled_maximum {z : N6.Configuration} (hz : N6.IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) (c d e : ℂ)
    (hp : N6.rootPolynomial (N6.scaleConfiguration α z) = N6.coefficientSextic 0 1 c d e) : c = 0 ∧ d = 0 := by
  let w := N6.scaleConfiguration α z
  let y := N6.dualConfiguration w
  have sta := N6.scaled_dualStationaryPair hz hα
  have r0 := stationaryR0_eq_liftY sta 1 c d e hp
  have rt := stationaryRT_eq_liftY sta 1 c d e hp
  obtain ⟨h0,h1,h2,h3⟩ := N6.scaled_maximum_rawStationaryEquations hz hα
  simp only [r0, rt, N6.ResultantMinors.coeff_liftY, projL3] at h0
  have eq0 : value (point 1 c d e 0) ChartIIE0 = 0 := (ChartIIE0_eval c d e).symm.trans h0
  simp only [r0, rt, N6.ResultantMinors.coeff_liftY, projL2, projC4] at h1
  have eq1 : value (point 1 c d e 0) ChartIIE1 = 0 := (ChartIIE1_eval c d e).symm.trans h1
  simp only [r0, rt, N6.ResultantMinors.coeff_liftY, projL1, projC3] at h2
  have eq2 : value (point 1 c d e 0) ChartIIE2 = 0 := (ChartIIE2_eval c d e).symm.trans h2
  simp only [r0, rt, N6.ResultantMinors.coeff_liftY, projL0, projC2] at h3
  have eq3 : value (point 1 c d e 0) ChartIIE3 = 0 := (ChartIIE3_eval c d e).symm.trans h3
  have ph4 := N6.physical_resultant_zero_coefficient w y _ (N6.scaled_dual_physical hz hα) 4 (by
    change (N6.rootPolynomial (N6.scaleConfiguration α z)).coeff _ = 0
    rw [hp]; simp [N6.coefficientSextic, Polynomial.coeff_C_mul, Polynomial.coeff_X_pow])
  dsimp only [w, y] at ph4
  simp only [r0, rt, N6.ResultantMinors.coeff_liftY, projC4] at ph4
  have eq4 : value (point 1 c d e 0) ChartIIR4 = 0 := (ChartIIR4_eval c d e).symm.trans ph4
  have de := discriminant_coeff_identity sta 1 c d e hp
  rw [projC6] at de
  have dn : value (point 1 c d e 0) ChartIIDelta ≠ 0 := by
    rw [← ChartIIDelta_eval, ← de]
    exact N6.complexDiscriminant_ne (N6.scaled_injective hz hα)
  exact ⟨ChartIIC_vanish c d e eq0 eq1 eq2 eq3 eq4 dn, ChartIID_vanish c d e eq0 eq1 eq2 eq3 eq4 dn⟩
#print axioms ChartII_of_scaled_maximum
end N6.Exceptional
