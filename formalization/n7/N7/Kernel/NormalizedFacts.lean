import N7.Kernel.MaximumGeometry

set_option autoImplicit false
namespace N7.Kernel
open N7.Analysis

theorem normalization_factor_ne : (Real.sqrt (6/7 : ℝ) : ℂ) ≠ 0 := by
  exact_mod_cast (Real.sqrt_pos.2 (by norm_num : (0 : ℝ) < 6/7)).ne'

theorem normalized_injective {z : Configuration} (hz : Function.Injective z) :
    Function.Injective (normalized z) := by
  intro i j hij
  exact hz (mul_left_cancel₀ normalization_factor_ne hij)

theorem delta_eq_norm (z : Configuration) :
    delta z = ∏ p ∈ pairs, ‖z p.1-z p.2‖^2 := by
  rw [←discriminant_eq_delta]
  simp only [discriminant, Complex.normSq_eq_norm_sq]

theorem injective_delta_pos {z : Configuration} (hz : Function.Injective z) :
    0 < delta z := by
  rw [←discriminant_eq_delta]
  exact discriminant_pos_of_injective hz

theorem normalized_delta (z : Configuration) :
    delta (normalized z) = (6/7 : ℝ)^21 * delta z := by
  rw [←discriminant_eq_delta, ←discriminant_eq_delta]
  change discriminant (fun i => (Real.sqrt (6/7 : ℝ) : ℂ)*z i) = _
  rw [discriminant_scale, Complex.normSq_eq_norm_sq, Complex.norm_real,
    Real.norm_eq_abs, sq_abs, Real.sq_sqrt (by norm_num)]

theorem sharp_scaling_identity : (6/7 : ℝ)^21 * sharpConstant = (6 : ℝ)^6 := by
  norm_num [sharpConstant]

theorem log_six_power : Real.log ((6 : ℝ)^6) = 6 * Real.log 6 := by
  rw [Real.log_pow]
  norm_num

theorem denormalized_point (z : Configuration) (i : Fin 7) :
    z i = (Real.sqrt (7/6 : ℝ) : ℂ) * normalized z i := by
  have h : Real.sqrt (7/6 : ℝ) * Real.sqrt (6/7 : ℝ) = 1 := by
    rw [←Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 7/6)]
    norm_num
  dsimp [normalized, scale]
  rw [←mul_assoc, ←Complex.ofReal_mul, h, Complex.ofReal_one, one_mul]

end N7.Kernel
