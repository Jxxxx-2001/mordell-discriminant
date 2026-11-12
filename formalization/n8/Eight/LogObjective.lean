import Eight.Variations

namespace MordellEight
open Finset Filter Set
open scoped Topology
set_option maxHeartbeats 0

noncomputable def logObjective (z : Configuration) : ℝ :=
  (∑ ij ∈ pairs, Real.log (‖z ij.1-z ij.2‖^2))-28*Real.log (energy z)

noncomputable def realMoment (z w : Configuration) : ℝ := ∑ i, realDot (z i) (w i)
noncomputable def pairLinear (z w : Configuration) : ℂ :=
  ∑ ij ∈ pairs, (w ij.1-w ij.2)/(z ij.1-z ij.2)
noncomputable def pairQuadratic (z w : Configuration) : ℂ :=
  ∑ ij ∈ pairs, ((w ij.1-w ij.2)/(z ij.1-z ij.2))^2

theorem injective_pair_ne {z : Configuration} (hz : Function.Injective z)
    (ij : Fin 8 × Fin 8) (hij : ij∈pairs) : z ij.1-z ij.2≠0 := by
  exact sub_ne_zero.mpr (fun h => (ne_of_lt (Finset.mem_filter.mp hij).2) (hz h))

theorem injective_delta_pos {z : Configuration} (hz : Function.Injective z) :
    0<delta z := by
  rw [delta_eq_norm]
  apply Finset.prod_pos
  intro ij hij
  exact sq_pos_of_pos (norm_pos_iff.mpr (injective_pair_ne hz ij hij))

theorem delta_pos_injective {z : Configuration} (hz : 0<delta z) :
    Function.Injective z := by
  intro i j h
  by_contra hn
  rcases lt_or_gt_of_ne hn with hi|hi
  · have he := collision_delta_zero z i j hi h
    linarith
  · have he := collision_delta_zero z j i hi h.symm
    linarith

theorem logObjective_eq {z : Configuration} (hz : Function.Injective z) (hE : energy z≠0) :
    logObjective z=Real.log (normalizedDiscriminant z) := by
  unfold logObjective normalizedDiscriminant
  rw [Real.log_div (injective_delta_pos hz).ne' (pow_ne_zero _ hE),Real.log_pow]
  rw [delta_eq_norm]
  congr 1
  exact (Real.log_prod (fun ij hij => pow_ne_zero _ (norm_ne_zero_iff.mpr (injective_pair_ne hz ij hij)))).symm

theorem affine_continuous (z w : Configuration) : Continuous (affine z w) := by
  unfold affine
  fun_prop

theorem affine_good_eventually {z : Configuration} (hE : 0<energy z)
    (hz : Function.Injective z) (w : Configuration) :
    ∀ᶠ s : ℝ in 𝓝 0, 0<energy (affine z w s) ∧ Function.Injective (affine z w s) := by
  have h1 : ContinuousAt (fun s => energy (affine z w s)) 0 :=
    (energy_continuous.comp (affine_continuous z w)).continuousAt
  have h2 : ContinuousAt (fun s => delta (affine z w s)) 0 :=
    (delta_continuous.comp (affine_continuous z w)).continuousAt
  have he : 0<energy (affine z w 0) := by simpa only [affine_zero] using hE
  have hd : 0<delta (affine z w 0) := by
    simpa only [affine_zero] using injective_delta_pos hz
  filter_upwards [h1.eventually (Ioi_mem_nhds he),h2.eventually (Ioi_mem_nhds hd)] with s hs ht
  exact ⟨hs,delta_pos_injective ht⟩

/-- No energy, stationarity, symmetry or collision assumption is added to the original maximum interface. -/
theorem maximum_logObjective_local {z : Configuration} (hE : energy z=8)
    (hm : ∀ w : Configuration, energy w=8 → delta w≤delta z)
    (w : Configuration) : IsLocalMax (fun s => logObjective (affine z w s)) 0 := by
  have hz := maximum_injective hm
  have he : 0<energy z := by rw [hE]; norm_num
  filter_upwards [affine_good_eventually he hz w] with s hs
  rw [affine_zero,logObjective_eq hs.2 hs.1.ne',logObjective_eq hz he.ne']
  apply Real.log_le_log
  · exact div_pos (injective_delta_pos hs.2) (pow_pos hs.1 _)
  · exact maximum_normalized hE hm _ hs.1

theorem affine_energy_hasDerivAt (z w : Configuration) (s : ℝ) :
    HasDerivAt (fun t => energy (affine z w t)) (2*realMoment (affine z w s) w) s := by
  have h := HasDerivAt.fun_sum (u := Finset.univ)
    (fun i _ => norm_affine_hasDerivAt (z i) (w i) s)
  simp only [energy_eq_norm,affine]
  convert h using 1
  simp only [realMoment,affine,Finset.mul_sum]

theorem affine_moment_hasDerivAt (z w : Configuration) (s : ℝ) :
    HasDerivAt (fun t => realMoment (affine z w t) w) (energy w) s := by
  rw [energy_eq_norm]
  exact HasDerivAt.fun_sum (fun i _ => realDot_affine_hasDerivAt (z i) (w i) s)

theorem affine_pair_difference (z w : Configuration) (s : ℝ) (i j : Fin 8) :
    affine z w s i-affine z w s j=(z i-z j)+(s : ℂ)*(w i-w j) := by
  dsimp [affine]
  ring

noncomputable def logObjectiveFirst (z w : Configuration) (s : ℝ) : ℝ :=
  (∑ ij ∈ pairs,logLineFirst (z ij.1-z ij.2) (w ij.1-w ij.2) s)-
    56*realMoment (affine z w s) w/energy (affine z w s)

theorem affine_logObjective_hasDerivAt (z w : Configuration) (s : ℝ)
    (hz : Function.Injective (affine z w s)) (hE : energy (affine z w s)≠0) :
    HasDerivAt (fun t => logObjective (affine z w t)) (logObjectiveFirst z w s) s := by
  have hp := HasDerivAt.fun_sum (u := pairs) (fun ij hij =>
    log_norm_affine_hasDerivAt (z ij.1-z ij.2) (w ij.1-w ij.2) s
      (by rw [←affine_pair_difference]; exact injective_pair_ne hz ij hij))
  have he := ((affine_energy_hasDerivAt z w s).log hE).const_mul 28
  have h := hp.sub he
  convert h using 1
  · funext t
    simp only [Pi.sub_apply,logObjective,affine_pair_difference]
  · dsimp [logObjectiveFirst]
    ring

theorem logObjectiveFirst_hasDerivAt (z w : Configuration) (s : ℝ)
    (hz : Function.Injective (affine z w s)) (hE : energy (affine z w s)≠0) :
    HasDerivAt (logObjectiveFirst z w)
      (-2*(pairQuadratic (affine z w s) w).re-
        56*energy w/energy (affine z w s)+
        112*(realMoment (affine z w s) w)^2/(energy (affine z w s))^2) s := by
  have hp := HasDerivAt.fun_sum (u := pairs) (fun ij hij =>
    logLineFirst_hasDerivAt (z ij.1-z ij.2) (w ij.1-w ij.2) s
      (by rw [←affine_pair_difference]; exact injective_pair_ne hz ij hij))
  have he := ((affine_moment_hasDerivAt z w s).const_mul 56).div
    (affine_energy_hasDerivAt z w s) hE
  have hpair : (∑ ij ∈ pairs,-2*(((w ij.1-w ij.2)/
      ((z ij.1-z ij.2)+(s : ℂ)*(w ij.1-w ij.2)))^2).re) =
      -2*(pairQuadratic (affine z w s) w).re := by
    simp only [pairQuadratic,Complex.re_sum,affine_pair_difference,Finset.mul_sum]
  have h := hp.sub he
  rw [hpair] at h
  convert h using 1
  field_simp [hE]
  ring

theorem logObjectiveFirst_zero (z w : Configuration) :
    logObjectiveFirst z w 0=2*(pairLinear z w).re-56*realMoment z w/energy z := by
  simp only [logObjectiveFirst,affine_zero,logLineFirst,Complex.ofReal_zero,zero_mul,add_zero]
  simp only [pairLinear,Complex.re_sum,←realDot_div_norm_sq,Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro ij hij
  ring

end MordellEight
