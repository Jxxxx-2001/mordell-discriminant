import N7.Kernel.MatrixBounds

set_option autoImplicit false
namespace N7.Kernel
open Checks

/-- Rational cubic-log anchors using the two already certified logarithms. -/
def logAnchor (p q : ℤ) : ℚ := (2 : ℚ)^p * (3 : ℚ)^q

def logAnchorInterval (p q : ℤ) : QInterval :=
  (QInterval.scale (p : ℚ) log2Interval).add (QInterval.scale (q : ℚ) log3Interval)

theorem logAnchor_pos (p q : ℤ) : 0 < (logAnchor p q : ℝ) := by
  simp only [logAnchor, Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat]
  positivity

theorem logAnchor_log (p q : ℤ) :
    Real.log (logAnchor p q : ℝ) = p * Real.log 2 + q * Real.log 3 := by
  simp only [logAnchor, Rat.cast_mul, Rat.cast_zpow, Rat.cast_ofNat]
  rw [Real.log_mul (zpow_ne_zero _ (by norm_num)) (zpow_ne_zero _ (by norm_num)),
    Real.log_zpow, Real.log_zpow]

theorem logAnchorInterval_sound (p q : ℤ) :
    (logAnchorInterval p q).Contains (Real.log (logAnchor p q : ℝ)) := by
  rw [logAnchor_log]
  have h := QInterval.add_sound
    (QInterval.scale_sound (p : ℚ) matrix_log2_contains)
    (QInterval.scale_sound (q : ℚ) matrix_log3_contains)
  simpa only [logAnchorInterval, Rat.cast_intCast] using h

#print axioms logAnchorInterval_sound
end N7.Kernel
