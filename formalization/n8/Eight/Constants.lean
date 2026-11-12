import Eight.Algebraic

namespace MordellEight
open Checks
set_option maxHeartbeats 0
set_option maxRecDepth 10000

theorem distance0_bounds : ((75302039/100000000) : ℝ) ≤ distanceParameters 0 ∧
    distanceParameters 0 ≤ (1882551/2500000) := by
  have ha := alpha_bounds
  norm_num [alphaLo,alphaHi] at ha
  have hslo : (6234898018/10000000000 : ℝ)^2 ≤ alpha^2 := by nlinarith
  have hshi : alpha^2 ≤ (6234898019/10000000000 : ℝ)^2 := by nlinarith
  norm_num [distanceParameters,cosineValues,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  constructor <;> nlinarith

theorem log0_lower_check : logCheck (75302039/100000000) (-283663/1000000) (-28366293/100000000) 24 = true := by
  decide +kernel
theorem log0_upper_check : logCheck (1882551/2500000) (-283663/1000000) (-28366293/100000000) 24 = true := by
  decide +kernel

theorem log0_bounds : ((-283663/1000000) : ℝ) ≤ logConstants 0 ∧
    logConstants 0 ≤ (-28366293/100000000) := by
  have hd := distance0_bounds
  have hl := (logCheck_sound _ _ _ _ log0_lower_check).1
  have hu := (logCheck_sound _ _ _ _ log0_upper_check).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] at hl hu
  unfold logConstants
  constructor
  · have hm := Real.log_le_log (show (0:ℝ) < (75302039/100000000) by norm_num) hd.1
    linarith
  · have hp : 0 < distanceParameters 0 := lt_of_lt_of_le (by norm_num) hd.1
    have hm := Real.log_le_log hp hd.2
    linarith

theorem distance1_bounds : ((122252093/50000000) : ℝ) ≤ distanceParameters 1 ∧
    distanceParameters 1 ≤ (61126047/25000000) := by
  have ha := alpha_bounds
  norm_num [alphaLo,alphaHi] at ha
  have hslo : (6234898018/10000000000 : ℝ)^2 ≤ alpha^2 := by nlinarith
  have hshi : alpha^2 ≤ (6234898019/10000000000 : ℝ)^2 := by nlinarith
  norm_num [distanceParameters,cosineValues,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  constructor <;> nlinarith

theorem log1_lower_check : logCheck (122252093/50000000) (44703111/50000000) (22351557/25000000) 24 = true := by
  decide +kernel
theorem log1_upper_check : logCheck (61126047/25000000) (44703111/50000000) (22351557/25000000) 24 = true := by
  decide +kernel

theorem log1_bounds : ((44703111/50000000) : ℝ) ≤ logConstants 1 ∧
    logConstants 1 ≤ (22351557/25000000) := by
  have hd := distance1_bounds
  have hl := (logCheck_sound _ _ _ _ log1_lower_check).1
  have hu := (logCheck_sound _ _ _ _ log1_upper_check).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] at hl hu
  unfold logConstants
  constructor
  · have hm := Real.log_le_log (show (0:ℝ) < (122252093/50000000) by norm_num) hd.1
    linarith
  · have hp : 0 < distanceParameters 1 := lt_of_lt_of_le (by norm_num) hd.1
    have hm := Real.log_le_log hp hd.2
    linarith

theorem distance2_bounds : ((380193773/100000000) : ℝ) ≤ distanceParameters 2 ∧
    distanceParameters 2 ≤ (15207751/4000000) := by
  have ha := alpha_bounds
  norm_num [alphaLo,alphaHi] at ha
  have hslo : (6234898018/10000000000 : ℝ)^2 ≤ alpha^2 := by nlinarith
  have hshi : alpha^2 ≤ (6234898019/10000000000 : ℝ)^2 := by nlinarith
  norm_num [distanceParameters,cosineValues,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  constructor <;> nlinarith

theorem log2_lower_check : logCheck (380193773/100000000) (33387771/25000000) (13355109/10000000) 24 = true := by
  decide +kernel
theorem log2_upper_check : logCheck (15207751/4000000) (33387771/25000000) (13355109/10000000) 24 = true := by
  decide +kernel

theorem log2_bounds : ((33387771/25000000) : ℝ) ≤ logConstants 2 ∧
    logConstants 2 ≤ (13355109/10000000) := by
  have hd := distance2_bounds
  have hl := (logCheck_sound _ _ _ _ log2_lower_check).1
  have hu := (logCheck_sound _ _ _ _ log2_upper_check).2
  norm_num only [Rat.cast_div, Rat.cast_ofNat, Rat.cast_neg] at hl hu
  unfold logConstants
  constructor
  · have hm := Real.log_le_log (show (0:ℝ) < (380193773/100000000) by norm_num) hd.1
    linarith
  · have hp : 0 < distanceParameters 2 := lt_of_lt_of_le (by norm_num) hd.1
    have hm := Real.log_le_log hp hd.2
    linarith

theorem distanceParameters_pos (j : Fin 3) : 0 < distanceParameters j := by
  fin_cases j
  · exact lt_of_lt_of_le (by norm_num) distance0_bounds.1
  · exact lt_of_lt_of_le (by norm_num) distance1_bounds.1
  · exact lt_of_lt_of_le (by norm_num) distance2_bounds.1

end MordellEight
