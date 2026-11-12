import Eight.Basics

namespace MordellEight
open Finset
set_option maxHeartbeats 0

noncomputable def centroid (z : Configuration) : ℂ :=
  ⟨(∑ i, (z i).re)/8,(∑ i, (z i).im)/8⟩
noncomputable def centered (z : Configuration) : Configuration := fun i => z i-centroid z
noncomputable def scale (r : ℝ) (z : Configuration) : Configuration := fun i => (r : ℂ)*z i

theorem norm_sq_coordinates (z : ℂ) : ‖z‖^2=z.re^2+z.im^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  ring

theorem real_shift_sum (a : Fin 8 → ℝ) (c : ℝ) :
    (∑ i, (a i-c)^2) = (∑ i, a i^2)-2*c*(∑ i,a i)+8*c^2 := by
  simp_rw [sub_sq]
  rw [Finset.sum_add_distrib,Finset.sum_sub_distrib]
  simp_rw [mul_assoc]
  rw [←Finset.mul_sum,←Finset.sum_mul]
  norm_num
  ring

theorem centered_energy (z : Configuration) : energy (centered z)=energy z-8*‖centroid z‖^2 := by
  simp only [energy_eq_norm,centered,norm_sq_coordinates,Complex.sub_re,Complex.sub_im,Finset.sum_add_distrib]
  rw [real_shift_sum,real_shift_sum]
  dsimp [centroid]
  ring

theorem centered_delta (z : Configuration) : delta (centered z)=delta z := by
  rw [delta_eq_norm,delta_eq_norm]
  apply Finset.prod_congr rfl
  intro ij hij
  have he : z ij.1-centroid z-(z ij.2-centroid z)=z ij.1-z ij.2 := by abel
  exact congrArg (fun w : ℂ => ‖w‖^2) he

theorem scale_energy (r : ℝ) (z : Configuration) : energy (scale r z)=r^2*energy z := by
  simp only [energy_eq_norm]
  unfold scale
  simp_rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [Finset.mul_sum]

theorem scale_delta (r : ℝ) (z : Configuration) :
    delta (scale r z)=r^56*delta z := by
  simp only [delta_eq_norm]
  unfold scale
  simp_rw [←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [Finset.prod_mul_distrib,Finset.prod_const,pairs_card,←pow_mul]

theorem centered_energy_pos {z : Configuration}
    (hm : ∀ w : Configuration, energy w=8 → delta w ≤ delta z) :
    0 < energy (centered z) := by
  have hp := maximum_delta_pos hm
  have hnn := energy_nonneg (centered z)
  by_contra h
  have he : energy (centered z)=0 := by linarith
  have hzero (i : Fin 8) : centered z i=0 := by
    have hs : ‖centered z i‖^2 ≤ energy (centered z) := by
      rw [energy_eq_norm]
      exact Finset.single_le_sum (s := Finset.univ) (f := fun j : Fin 8 => ‖centered z j‖^2)
        (fun j _ => sq_nonneg (‖centered z j‖)) (Finset.mem_univ i)
    rw [he] at hs
    apply norm_eq_zero.mp
    nlinarith [norm_nonneg (centered z i)]
  have hdisc := collision_delta_zero (centered z) 0 1 (by norm_num)
    ((hzero 0).trans (hzero 1).symm)
  rw [centered_delta] at hdisc
  linarith

/-- Centering is forced at every global maximizer; no nondegeneracy assumption is added. -/
theorem maximum_centered {z : Configuration} (hz : energy z=8)
    (hm : ∀ w : Configuration, energy w=8 → delta w ≤ delta z) : centroid z=0 := by
  by_contra hc
  have he := centered_energy_pos hm
  have hvar : 0 < ‖centroid z‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
  have hlt : energy (centered z) < 8 := by rw [centered_energy,hz]; nlinarith
  have hratio : (1 : ℝ) < 8/energy (centered z) := (one_lt_div he).mpr hlt
  let r : ℝ := Real.sqrt (8/energy (centered z))
  have hr : 1 < r := Real.lt_sqrt_of_sq_lt (by simpa using hratio)
  have hrsq : r^2=8/energy (centered z) := Real.sq_sqrt (by positivity)
  have hscaled : energy (scale r (centered z))=8 := by
    rw [scale_energy,hrsq]
    exact div_mul_cancel₀ 8 he.ne'
  have hd := hm (scale r (centered z)) hscaled
  rw [scale_delta,centered_delta] at hd
  have hp := maximum_delta_pos hm
  have hpow : 1 < r^56 := one_lt_pow₀ hr (by decide)
  nlinarith

theorem sum_eq_eight_centroid (z : Configuration) : (∑ i,z i)=8*centroid z := by
  apply Complex.ext <;> simp [centroid] <;> ring

theorem maximum_sum_zero {z : Configuration} (hz : energy z=8)
    (hm : ∀ w : Configuration, energy w=8 → delta w ≤ delta z) : (∑ i,z i)=0 := by
  rw [sum_eq_eight_centroid,maximum_centered hz hm,mul_zero]

noncomputable def normalizedDiscriminant (z : Configuration) : ℝ := delta z/(energy z)^28

/-- Scaling turns every spherical maximizer into a maximum of the scale-invariant objective. -/
theorem maximum_normalized {z : Configuration} (hz : energy z=8)
    (hm : ∀ w : Configuration, energy w=8 → delta w ≤ delta z)
    (w : Configuration) (hw : 0 < energy w) : normalizedDiscriminant w ≤ normalizedDiscriminant z := by
  let r : ℝ := Real.sqrt (8/energy w)
  have hs : r^2=8/energy w := Real.sq_sqrt (by positivity)
  have hE : energy (scale r w)=8 := by
    rw [scale_energy,hs]
    exact div_mul_cancel₀ 8 hw.ne'
  have h := hm (scale r w) hE
  rw [scale_delta] at h
  have hp : r^56=8^28/(energy w)^28 := by
    calc
      _ = (r^2)^28 := by rw [←pow_mul]
      _ = _ := by rw [hs,div_pow]
  rw [hp] at h
  unfold normalizedDiscriminant
  rw [hz]
  apply (le_div_iff₀ (by norm_num : (0 : ℝ) < 8^28)).mpr
  have heq : delta w/(energy w)^28*8^28 = 8^28/(energy w)^28*delta w := by ring
  rw [heq]
  exact h

end MordellEight
