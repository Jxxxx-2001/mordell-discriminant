import Eight.AlgebraicRefinement

namespace MordellEight.RefinedConstants.L1
open Checks
set_option maxHeartbeats 0
set_option maxRecDepth 100000
def distanceBounds : QInterval := ⟨(24450418679126288085778051/10000000000000000000000000),(6112604669781572021444513/2500000000000000000000000)⟩
def logBounds : QInterval := ⟨(89406224667086893577431/100000000000000000000000),(11175778083385861697179/12500000000000000000000)⟩
theorem distanceBounds_sound : distanceBounds.Contains (distanceParameters 1) := by
  have ha := alphaRefined_sound
  norm_num [alphaRefined,QInterval.Contains] at ha
  have hslo : ((155872450464683382631251221001/250000000000000000000000000000):ℝ)^2≤alpha^2 := by nlinarith [alpha_coarse.1]
  have hshi : alpha^2≤((124697960371746706105000976801/200000000000000000000000000000):ℝ)^2 := by nlinarith [alpha_coarse.1]
  norm_num [distanceBounds,QInterval.Contains,distanceParameters,cosineValues,
    Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  constructor <;> nlinarith
theorem lower_checked : logCheck distanceBounds.lo logBounds.lo logBounds.hi 64=true := by
  decide +kernel
theorem upper_checked : logCheck distanceBounds.hi logBounds.lo logBounds.hi 64=true := by
  decide +kernel
theorem logBounds_sound : logBounds.Contains (logConstants 1) := by
  have hd := distanceBounds_sound
  have hl := (logCheck_sound _ _ _ _ lower_checked).1
  have hu := (logCheck_sound _ _ _ _ upper_checked).2
  have hp : (0:ℝ)<(distanceBounds.lo:ℝ) := by norm_num [distanceBounds]
  have hpos : 0<distanceParameters 1 := hp.trans_le hd.1
  exact ⟨hl.trans (Real.log_le_log hp hd.1),(Real.log_le_log hpos hd.2).trans hu⟩
end MordellEight.RefinedConstants.L1
