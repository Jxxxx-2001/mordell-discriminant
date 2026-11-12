import Eight.Operator

namespace MordellEight
open Finset
set_option maxHeartbeats 0

theorem laplacian_sum_zero (z w : Configuration) : ∑ i, laplacian z w i=0 := by
  unfold laplacian
  rw [double_sum_pairs (fun i j => (w i-w j)/(z i-z j)^2) (by intro i; simp)]
  apply Finset.sum_eq_zero
  intro ij hij
  rw [show z ij.2-z ij.1=-(z ij.1-z ij.2) by ring,neg_sq]
  ring

theorem laplacian_centered (z w : Configuration) : laplacian z (centered w)=laplacian z w := by
  funext i
  apply Finset.sum_congr rfl
  intro j hj
  congr 1
  dsimp [centered]
  ring

theorem laplacian_impulse (z : Configuration) (i j : Fin 8) (hij : i≠j) :
    laplacian z (impulse j) i= -1/(z i-z j)^2 := by
  simp [laplacian,impulse,hij,ite_div,apply_ite]

theorem centroid_impulse (i : Fin 8) : centroid (impulse i)=(1/8 : ℂ) := by
  apply Complex.ext <;> norm_num [centroid,impulse,apply_ite]

theorem energy_impulse (i : Fin 8) : energy (impulse i)=1 := by
  simp [energy,impulse,apply_ite]

theorem energy_projected_impulse (i : Fin 8) : energy (centered (impulse i))=7/8 := by
  rw [centered_energy,energy_impulse,centroid_impulse]
  norm_num

theorem innerMoment_centered_left (v w : Configuration) :
    innerMoment (centered v) w=innerMoment v w-star (centroid v)*(∑ i,w i) := by
  simp only [innerMoment,centered,star_sub,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]

theorem innerMoment_projected_impulse (i : Fin 8) (w : Configuration) (hw : ∑ j,w j=0) :
    innerMoment (centered (impulse i)) w=w i := by
  rw [innerMoment_centered_left,hw,mul_zero,sub_zero]
  simp [innerMoment,impulse]

/-- Sharp pair separation forced by the full-space second-order condition. -/
theorem maximum_distance_sq {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z)
    (i j : Fin 8) (hij : i≠j) : (16/49 : ℝ)≤‖z i-z j‖^2 := by
  have hc := innerMoment_cauchy (centered (impulse i)) (laplacian z (centered (impulse j)))
  rw [innerMoment_projected_impulse _ _ (laplacian_sum_zero _ _),energy_projected_impulse] at hc
  have ho := maximum_laplacian_energy hz hm (centered (impulse j))
  rw [energy_projected_impulse] at ho
  have hab : ‖laplacian z (centered (impulse j)) i‖^2≤(2401/256 : ℝ) := by linarith
  rw [laplacian_centered,laplacian_impulse z i j hij] at hab
  simp only [norm_div,norm_neg,norm_one,norm_pow,div_pow,one_pow] at hab
  have hd : 0<‖z i-z j‖^2 := sq_pos_of_pos (norm_pos_iff.mpr
    (sub_ne_zero.mpr (fun he => hij (maximum_injective hm he))))
  have hh : 1≤(2401/256 : ℝ)*(‖z i-z j‖^2)^2 := (div_le_iff₀ (sq_pos_of_pos hd)).mp hab
  by_contra hn
  have hlt : ‖z i-z j‖^2<(16/49 : ℝ) := lt_of_not_ge hn
  nlinarith [mul_pos (sub_pos.mpr hlt) (show (0 : ℝ)<16/49+‖z i-z j‖^2 by positivity)]

noncomputable def normalized (z : Configuration) : Configuration := scale (Real.sqrt (7/8 : ℝ)) z

theorem normalized_energy {z : Configuration} (hz : energy z=8) : energy (normalized z)=7 := by
  rw [normalized,scale_energy,hz,Real.sq_sqrt (by norm_num)]
  norm_num

theorem normalized_distance (z : Configuration) (i j : Fin 8) :
    ‖normalized z i-normalized z j‖^2=(7/8 : ℝ)*‖z i-z j‖^2 := by
  simp only [normalized,scale,←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [Real.sq_sqrt (by norm_num)]

theorem maximum_normalized_distance {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z)
    (i j : Fin 8) (hij : i≠j) : (2/7 : ℝ)≤‖normalized z i-normalized z j‖^2 := by
  rw [normalized_distance]
  have h := maximum_distance_sq hz hm i j hij
  linarith

theorem realDot_sq_le (a b : ℂ) : (realDot a b)^2≤‖a‖^2*‖b‖^2 := by
  rw [norm_sq_coordinates,norm_sq_coordinates]
  dsimp [realDot]
  nlinarith [sq_nonneg (a.re*b.im-a.im*b.re)]

theorem norm_sub_eq_realDot (a b : ℂ) : ‖a-b‖^2=‖a‖^2+‖b‖^2-2*realDot a b := by
  simp only [norm_sq_coordinates,Complex.sub_re,Complex.sub_im,realDot]
  ring

noncomputable def pairPoint (z : Configuration) (i j : Fin 8) : Fin 3 → ℝ :=
  ![‖normalized z i‖^2,‖normalized z j‖^2,realDot (normalized z i) (normalized z j)]

end MordellEight
