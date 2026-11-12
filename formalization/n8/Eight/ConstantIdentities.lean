import Eight.Constants

namespace MordellEight

theorem distanceParameters_product :
    distanceParameters 0 * distanceParameters 1 * distanceParameters 2 = 7 := by
  have h := alpha_equation
  unfold cubic at h
  norm_num [distanceParameters,cosineValues,Matrix.cons_val_two,Matrix.vecHead,Matrix.vecTail]
  linear_combination (4*alpha^2-4*alpha-1)*h

theorem logConstants_sum : logConstants 0 + logConstants 1 + logConstants 2 = Real.log 7 := by
  unfold logConstants
  rw [←Real.log_mul (distanceParameters_pos 0).ne' (distanceParameters_pos 1).ne',
      ←Real.log_mul (mul_pos (distanceParameters_pos 0) (distanceParameters_pos 1)).ne'
        (distanceParameters_pos 2).ne', distanceParameters_product]

end MordellEight
