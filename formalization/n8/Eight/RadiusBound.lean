import Eight.Statement

namespace MordellEight

noncomputable def radiusUpper : ℝ := 965267/524288
def radiusPolynomial (s : ℝ) : ℝ := 882*s^3-2352*s^2+1755*s-1496
noncomputable def originalRadiusUpper : ℝ := 8*radiusUpper/7

theorem originalRadiusUpper_gt_two : (2:ℝ)<originalRadiusUpper := by
  norm_num [originalRadiusUpper,radiusUpper]

theorem radiusPolynomial_at_upper_pos : 0<radiusPolynomial originalRadiusUpper := by
  norm_num [radiusPolynomial,originalRadiusUpper,radiusUpper]

theorem radiusPolynomial_strict_above_two {x y : ℝ} (hx : 2≤x) (hxy : x<y) :
    radiusPolynomial x < radiusPolynomial y := by
  have hy : 2≤y := hx.trans hxy.le
  have hx2 : 2*x≤x^2 := by nlinarith
  have hy2 : 2*y≤y^2 := by nlinarith
  have hxy2 : 2*x+2*y-4≤x*y := by
    nlinarith [mul_nonneg (sub_nonneg.mpr hx) (sub_nonneg.mpr hy)]
  have hf : 0<882*(y^2+x*y+x^2)-2352*(y+x)+1755 := by nlinarith
  have hp := mul_pos (sub_pos.mpr hxy) hf
  have he : radiusPolynomial y-radiusPolynomial x =
      (y-x)*(882*(y^2+x*y+x^2)-2352*(y+x)+1755) := by
    unfold radiusPolynomial
    ring
  linarith

/-- The eight-point rational radial cutoff needs no external Sturm calculation. -/
theorem radius_bound_of_polynomial {s : ℝ} (hs : radiusPolynomial s≤0) :
    s≤originalRadiusUpper := by
  by_contra h
  have hlt := radiusPolynomial_strict_above_two originalRadiusUpper_gt_two.le (lt_of_not_ge h)
  linarith [radiusPolynomial_at_upper_pos]

theorem normalized_radius_bound_of_polynomial {s : ℝ} (hs : radiusPolynomial s≤0) :
    (7/8)*s≤radiusUpper := by
  have h := radius_bound_of_polynomial hs
  unfold originalRadiusUpper at h
  linarith

end MordellEight
