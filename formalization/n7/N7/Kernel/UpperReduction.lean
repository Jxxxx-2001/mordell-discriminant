import N7.Kernel.NormalizedFacts
import N7.Kernel.Sum

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace N7.Kernel
open Finset N7.Analysis

variable (Q : Fin 6 → Matrix (Fin 4) (Fin 4) ℝ)

/-- A pair bound for every genuine maximizer. Its proof must cover the whole
necessary domain; a finite sample or a list of stationary candidates is insufficient. -/
def MaximumMajorant : Prop := ∀ {z : Configuration}, IsGlobalMaximum z →
  ∀ i j : Fin 7, i ≠ j →
    Real.log (‖normalized z i-normalized z j‖^2) ≤
      majorantFromMatrices Q (‖normalized z i‖^2) (‖normalized z j‖^2)
        (normalized z i * star (normalized z j)).re

theorem maximum_log_sum_le_majorant (hbound : MaximumMajorant Q)
    {z : Configuration} (hz : IsGlobalMaximum z) :
    Real.log (delta (normalized z)) ≤ ∑ ij ∈ pairs,
      majorantFromMatrices Q (‖normalized z ij.1‖^2) (‖normalized z ij.2‖^2)
        (normalized z ij.1 * star (normalized z ij.2)).re := by
  have hi := normalized_injective (global_maximum_injective hz)
  have hlog : Real.log (delta (normalized z)) =
      ∑ ij ∈ pairs, Real.log (‖normalized z ij.1-normalized z ij.2‖^2) := by
    rw [delta_eq_norm]
    apply Real.log_prod
    intro ij hij
    exact pow_ne_zero _ (norm_ne_zero_iff.mpr (sub_ne_zero.mpr
      (hi.ne (ne_of_lt (Finset.mem_filter.mp hij).2))))
  rw [hlog]
  exact Finset.sum_le_sum (fun ij hij => hbound hz ij.1 ij.2
    (ne_of_lt (Finset.mem_filter.mp hij).2))

theorem maximum_upper_of_majorant (hQ : ∀ k, (Q k).PosDef)
    (hbound : MaximumMajorant Q) {z : Configuration} (hz : IsGlobalMaximum z) :
    delta z ≤ sharpConstant := by
  have he : energy z = 7 := by simpa only [normSum_eq_energy] using hz.1
  have hl := (maximum_log_sum_le_majorant Q hbound hz).trans
    (majorant_pair_sum_le Q hQ (normalized z) (normalized_energy he))
  have hp := injective_delta_pos (normalized_injective (global_maximum_injective hz))
  have hd : delta (normalized z) ≤ (6 : ℝ)^6 := by
    apply (Real.log_le_log_iff hp (by norm_num)).mp
    rwa [log_six_power]
  rw [normalized_delta, ←sharp_scaling_identity] at hd
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ) < (6/7 : ℝ)^21)).mp hd

theorem upper_of_majorant (hQ : ∀ k, (Q k).PosDef) (hbound : MaximumMajorant Q)
    {z : Configuration} (hz : energy z = 7) : delta z ≤ sharpConstant := by
  obtain ⟨m, hmE, hm⟩ := exists_global_maximum
  have hzm := hm z (by rwa [normSum_eq_energy])
  rw [discriminant_eq_delta, discriminant_eq_delta] at hzm
  exact hzm.trans (maximum_upper_of_majorant Q hQ hbound ⟨hmE, hm⟩)

theorem equality_momentVectors_of_majorant (hQ : ∀ k, (Q k).PosDef)
    (hbound : MaximumMajorant Q) {z : Configuration}
    (hz : energy z = 7) (he : delta z = sharpConstant) :
    ∀ k : Fin 6, momentVector (normalized z) k = 0 := by
  have hm : IsGlobalMaximum z := by
    refine ⟨by rwa [normSum_eq_energy], ?_⟩
    intro w hw
    rw [discriminant_eq_delta, discriminant_eq_delta, he]
    exact upper_of_majorant Q hQ hbound (by rwa [←normSum_eq_energy])
  have hd : delta (normalized z) = (6 : ℝ)^6 := by
    rw [normalized_delta, he, sharp_scaling_identity]
  have hs := maximum_log_sum_le_majorant Q hbound hm
  rw [hd, log_six_power, majorant_pair_sum Q hQ (normalized z) (normalized_energy hz)] at hs
  have hn := kernel_double_sum_nonneg Q hQ (normalized z)
  have hk : (∑ i, ∑ j, kernelFromMatrices Q (‖normalized z i‖^2)
      (‖normalized z j‖^2) (normalized z i * star (normalized z j)).re) = 0 := by
    linarith
  exact (kernel_double_sum_zero_iff Q hQ (normalized z)).mp hk

#print axioms upper_of_majorant
#print axioms equality_momentVectors_of_majorant
end N7.Kernel
