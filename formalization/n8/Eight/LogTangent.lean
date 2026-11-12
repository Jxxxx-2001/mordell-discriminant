import Eight.Checks.LogBounds

namespace MordellEight

theorem log_le_tangent {d a upper : ℝ} (hd : 0<d) (ha : 0<a)
    (hu : Real.log a≤upper) : Real.log d≤upper-1+d/a := by
  have h := Real.log_le_sub_one_of_pos (div_pos hd ha)
  rw [Real.log_div hd.ne' ha.ne'] at h
  linarith

end MordellEight
