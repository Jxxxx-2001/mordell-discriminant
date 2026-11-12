import Eight.LogObjective
import Eight.Invariance

namespace MordellEight
open Finset Filter Set
open scoped Topology
set_option maxHeartbeats 0

noncomputable def innerMoment (z w : Configuration) : ℂ := ∑ i, (star (z i))*w i

theorem realMoment_eq (z w : Configuration) : realMoment z w=(innerMoment z w).re := by
  simp only [realMoment,innerMoment,Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [realDot,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

theorem innerMoment_scale (z w : Configuration) (c : ℂ) :
    innerMoment z (complexScale c w)=c*innerMoment z w := by
  simp only [innerMoment,complexScale,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i hi
  ring

theorem pairLinear_scale (z w : Configuration) (c : ℂ) :
    pairLinear z (complexScale c w)=c*pairLinear z w := by
  simp only [pairLinear,complexScale,←mul_sub,mul_div_assoc,Finset.mul_sum]

theorem pairQuadratic_scale (z w : Configuration) (c : ℂ) :
    pairQuadratic z (complexScale c w)=c^2*pairQuadratic z w := by
  simp only [pairQuadratic,complexScale,←mul_sub,mul_div_assoc,mul_pow,Finset.mul_sum]

theorem maximum_pairLinear_re {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z)
    (w : Configuration) : (pairLinear z w).re=(7/2)*realMoment z w := by
  have hi := maximum_injective hm
  have hE : energy z≠0 := by rw [hz]; norm_num
  have hf := affine_logObjective_hasDerivAt z w 0 (by simpa only [affine_zero] using hi)
    (by simpa only [affine_zero] using hE)
  have h := (maximum_logObjective_local hz hm w).hasDerivAt_eq_zero hf
  rw [logObjectiveFirst_zero,hz] at h
  linarith

/-- Full complex first-order equation for every variation, not just symmetric variations. -/
theorem maximum_pairLinear {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z)
    (w : Configuration) : pairLinear z w=(7/2)*innerMoment z w := by
  have hr := maximum_pairLinear_re hz hm w
  rw [realMoment_eq] at hr
  have hi := maximum_pairLinear_re hz hm (complexScale Complex.I w)
  rw [pairLinear_scale,realMoment_eq,innerMoment_scale] at hi
  apply Complex.ext
  · simpa using hr
  · simp only [Complex.mul_re,Complex.I_re,Complex.I_im,zero_mul,one_mul,zero_sub] at hi
    simpa using (show (pairLinear z w).im=(7/2)*(innerMoment z w).im by linarith)

/-- The normalized logarithmic objective has the required second derivative at the maximum. -/
theorem maximum_log_second {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z)
    (w : Configuration) :
    -2*(pairQuadratic z w).re-7*energy w+(7/4)*(realMoment z w)^2≤0 := by
  have hi := maximum_injective hm
  have hE : 0<energy z := by rw [hz]; norm_num
  have hf := affine_logObjective_hasDerivAt z w 0 (by simpa only [affine_zero] using hi)
    (by simpa only [affine_zero] using hE.ne')
  have hlocal := maximum_logObjective_local hz hm w
  have heq : (fun s => deriv (fun t => logObjective (affine z w t)) s) =ᶠ[𝓝 0]
      logObjectiveFirst z w := by
    filter_upwards [affine_good_eventually hE hi w] with s hs
    exact (affine_logObjective_hasDerivAt z w s hs.2 hs.1.ne').deriv
  have hsecond := logObjectiveFirst_hasDerivAt z w 0
    (by simpa only [affine_zero] using hi) (by simpa only [affine_zero] using hE.ne')
  have hn := localMax_second_nonpos hlocal hf.continuousAt
  rw [heq.deriv_eq,hsecond.deriv,affine_zero,hz] at hn
  norm_num at hn
  linarith

/-- Full-space necessary bound, allowing degenerate second-order directions. -/
theorem maximum_pairQuadratic_re_bounds {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z)
    (w : Configuration) : -(7/2)*energy w≤(pairQuadratic z w).re ∧
      (pairQuadratic z w).re≤(7/2)*energy w := by
  have h := maximum_log_second hz hm w
  have hlo : -(7/2)*energy w≤(pairQuadratic z w).re := by nlinarith [sq_nonneg (realMoment z w)]
  have hI := maximum_log_second hz hm (complexScale Complex.I w)
  rw [pairQuadratic_scale,energy_complexScale] at hI
  norm_num at hI
  exact ⟨hlo,by nlinarith [sq_nonneg (realMoment z (complexScale Complex.I w))]⟩

end MordellEight
