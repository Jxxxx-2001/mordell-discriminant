import Eight.PairDomain

namespace MordellEight
open Finset
set_option maxHeartbeats 0

theorem normalized_injective {z : Configuration} (hz : Function.Injective z) :
    Function.Injective (normalized z) := by
  have hr : Real.sqrt (7/8 : ℝ)≠0 := (Real.sqrt_pos.mpr (by norm_num)).ne'
  have hc : (Real.sqrt (7/8 : ℝ) : ℂ)≠0 := by exact_mod_cast hr
  intro i j hij
  apply hz
  exact mul_left_cancel₀ hc hij

theorem normalized_delta (z : Configuration) :
    delta (normalized z)=(7/8 : ℝ)^28*delta z := by
  rw [normalized,scale_delta,show (56 : ℕ)=2*28 by norm_num,pow_mul,
    Real.sq_sqrt (by norm_num)]

theorem sharp_scaling_identity : (7/8 : ℝ)^28*sharpConstant=(7 : ℝ)^7 := by
  norm_num [sharpConstant]

theorem log_seven_power : Real.log ((7 : ℝ)^7)=7*Real.log 7 := by
  rw [Real.log_pow]
  norm_num

theorem normalized_sum_zero {z : Configuration} (hz : (∑ i,z i)=0) : (∑ i,normalized z i)=0 := by
  simp only [normalized,scale,←Finset.mul_sum,hz,mul_zero]

theorem radius_binary_origin {z : Configuration} (hE : energy z=7)
    (hr : ∀ i,‖z i‖^2=0 ∨ ‖z i‖^2=1) : ∃ i,z i=0 := by
  by_contra hn
  push_neg at hn
  have hones (i : Fin 8) : ‖z i‖^2=1 :=
    (hr i).resolve_left (pow_ne_zero _ (norm_ne_zero_iff.mpr (hn i)))
  have htotal : energy z=8 := by simp only [energy_eq_norm,hones]; norm_num
  linarith

theorem radius_binary_unique_origin {z : Configuration} (hE : energy z=7)
    (hr : ∀ i,‖z i‖^2=0 ∨ ‖z i‖^2=1) (hi : Function.Injective z) :
    ∃! i,z i=0 := by
  obtain ⟨i,hiz⟩ := radius_binary_origin hE hr
  exact ⟨i,hiz,fun j hj => hi (hj.trans hiz.symm)⟩

theorem radius_binary_other_unit {z : Configuration}
    (hr : ∀ i,‖z i‖^2=0 ∨ ‖z i‖^2=1) (hi : Function.Injective z)
    {i : Fin 8} (hiz : z i=0) {j : Fin 8} (hij : j≠i) : ‖z j‖^2=1 := by
  have hjz : z j≠0 := fun he => hij (hi (he.trans hiz.symm))
  exact (hr j).resolve_left (pow_ne_zero _ (norm_ne_zero_iff.mpr hjz))

end MordellEight
