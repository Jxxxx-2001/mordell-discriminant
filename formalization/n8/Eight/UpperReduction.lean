import Eight.Normalized
import Eight.KernelSum

namespace MordellEight
open Finset
set_option maxHeartbeats 0

/-- Remaining obligation, not an axiom or an already proved assertion. -/
def DomainMajorant : Prop := ∀ u v t : ℝ, PairDomain u v t →
  Real.log (u+v-2*t)≤majorantFromMatrices u v t

theorem realDot_eq_re_mul_conj (a b : ℂ) : realDot a b=(a*star b).re := by
  simp [realDot,Complex.mul_re,Complex.star_def]

theorem maximum_pair_majorant (hbound : DomainMajorant) {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration,energy y=8 → delta y≤delta z)
    (i j : Fin 8) (hij : i≠j) :
    Real.log (‖normalized z i-normalized z j‖^2)≤
      majorantFromMatrices (‖normalized z i‖^2) (‖normalized z j‖^2)
        (normalized z i*star (normalized z j)).re := by
  have h := hbound _ _ _ (maximum_pairDomain hz hm i j hij)
  rw [←norm_sub_eq_realDot,realDot_eq_re_mul_conj] at h
  exact h

theorem maximum_log_sum_le_majorant (hbound : DomainMajorant) {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration,energy y=8 → delta y≤delta z) :
    Real.log (delta (normalized z))≤∑ ij ∈ pairs,
      majorantFromMatrices (‖normalized z ij.1‖^2) (‖normalized z ij.2‖^2)
        (normalized z ij.1*star (normalized z ij.2)).re := by
  have hi := normalized_injective (maximum_injective hm)
  have hlog : Real.log (delta (normalized z))=
      ∑ ij ∈ pairs,Real.log (‖normalized z ij.1-normalized z ij.2‖^2) :=
    by
      rw [delta_eq_norm]
      exact Real.log_prod (fun ij hij => pow_ne_zero _ (norm_ne_zero_iff.mpr (injective_pair_ne hi ij hij)))
  rw [hlog]
  exact Finset.sum_le_sum (fun ij hij => maximum_pair_majorant hbound hz hm ij.1 ij.2
    (ne_of_lt (Finset.mem_filter.mp hij).2))

theorem maximum_upper_of_domainMajorant (hbound : DomainMajorant) {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration,energy y=8 → delta y≤delta z) :
    delta z≤sharpConstant := by
  have hl := (maximum_log_sum_le_majorant hbound hz hm).trans
    (majorant_pair_sum_le (normalized z) (normalized_energy hz))
  have hp := injective_delta_pos (normalized_injective (maximum_injective hm))
  have hd : delta (normalized z)≤(7 : ℝ)^7 := by
    apply (Real.log_le_log_iff hp (by norm_num)).mp
    rwa [log_seven_power]
  rw [normalized_delta,←sharp_scaling_identity] at hd
  exact (mul_le_mul_iff_right₀ (by positivity : (0 : ℝ)<(7/8 : ℝ)^28)).mp hd

/-- Conditional reduction only: the continuous-domain majorant remains an explicit parameter. -/
theorem upper_of_domainMajorant (hbound : DomainMajorant) (z : Configuration) (hz : energy z=8) :
    delta z≤sharpConstant := by
  obtain ⟨m,hmE,hm⟩ := exists_global_maximum
  exact (hm z hz).trans (maximum_upper_of_domainMajorant hbound hmE hm)

theorem equality_maximum_of_domainMajorant (hbound : DomainMajorant) {z : Configuration}
    (he : delta z=sharpConstant) :
    ∀ y : Configuration,energy y=8 → delta y≤delta z := by
  intro y hy
  rw [he]
  exact upper_of_domainMajorant hbound y hy

theorem equality_momentVectors_of_domainMajorant (hbound : DomainMajorant) {z : Configuration}
    (hz : energy z=8) (he : delta z=sharpConstant) :
    ∀ k : Fin 7,momentVector (normalized z) k=0 := by
  have hm := equality_maximum_of_domainMajorant hbound he
  have hd : delta (normalized z)=(7 : ℝ)^7 := by
    rw [normalized_delta,he,sharp_scaling_identity]
  have hs := maximum_log_sum_le_majorant hbound hz hm
  rw [hd,log_seven_power,majorant_pair_sum (normalized z) (normalized_energy hz)] at hs
  have hn := kernel_double_sum_nonneg (normalized z)
  have hk : (∑ i,∑ j,kernelFromMatrices (‖normalized z i‖^2) (‖normalized z j‖^2)
      (normalized z i*star (normalized z j)).re)=0 := by linarith
  exact (kernel_double_sum_zero_iff (normalized z)).mp hk

theorem equality_radial_shape_of_domainMajorant (hbound : DomainMajorant) {z : Configuration}
    (hz : energy z=8) (he : delta z=sharpConstant) :
    ∃ i : Fin 8,normalized z i=0 ∧
      (∀ j : Fin 8,j≠i → ‖normalized z j‖^2=1) ∧
      ∀ k : Fin 7,k≠0 → (∑ j,(normalized z j)^k.val)=0 := by
  have hm := equality_maximum_of_domainMajorant hbound he
  have hi := normalized_injective (maximum_injective hm)
  have hk := equality_momentVectors_of_domainMajorant hbound hz he
  have hr := kernel_zero_radius_classification (normalized z) (hk 0)
  obtain ⟨i,hiz⟩ := radius_binary_origin (normalized_energy hz) hr
  refine ⟨i,hiz,fun j hj => radius_binary_other_unit hr hi hiz hj,?_⟩
  intro k hkn
  rw [←momentVector_first (normalized z) k hkn,hk k]
  rfl

end MordellEight
