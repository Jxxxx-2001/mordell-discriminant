import N7.Kernel.MaximumOperator
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace N7.Kernel
open Finset N7.Analysis
noncomputable def centroid (z : Configuration) : ℂ := (∑ i,z i)/7
noncomputable def centered (z : Configuration) : Configuration := fun i => z i-centroid z
noncomputable def scale (r : ℝ) (z : Configuration) : Configuration := fun i => (r:ℂ)*z i
noncomputable def realDot (a b : ℂ) : ℝ := (a*star b).re

theorem centered_normSum (z : Configuration) : normSum (centered z)=normSum z-7*‖centroid z‖^2 := by
  change normSum (center z)=_
  rw [normSum_center]
  simp only [centroid,norm_div,div_pow,Complex.normSq_eq_norm_sq]
  norm_num
  ring

theorem scale_normSum (r : ℝ) (z : Configuration) : normSum (scale r z)=r^2*normSum z := by
  change normSum (fun i => (r:ℂ)*z i)=_
  rw [normSum_scale,Complex.normSq_eq_norm_sq,Complex.norm_real,Real.norm_eq_abs,sq_abs]

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

theorem laplacian_impulse (z : Configuration) (i j : Fin 7) (hij : i≠j) :
    laplacian z (impulse j) i= -1/(z i-z j)^2 := by
  simp [laplacian,impulse,hij,ite_div,apply_ite]

theorem centroid_impulse (i : Fin 7) : centroid (impulse i)=(1/7 : ℂ) := by
  apply Complex.ext <;> norm_num [centroid,impulse,apply_ite]

theorem energy_impulse (i : Fin 7) : normSum (impulse i)=1 := by
  simp [normSum,impulse,apply_ite]

theorem energy_projected_impulse (i : Fin 7) : normSum (centered (impulse i))=6/7 := by
  rw [centered_normSum,energy_impulse,centroid_impulse]
  norm_num

theorem innerMoment_centered_left (v w : Configuration) :
    innerMoment (centered v) w=innerMoment v w-star (centroid v)*(∑ i,w i) := by
  simp only [innerMoment,centered,star_sub,sub_mul,Finset.sum_sub_distrib,Finset.mul_sum]

theorem innerMoment_projected_impulse (i : Fin 7) (w : Configuration) (hw : ∑ j,w j=0) :
    innerMoment (centered (impulse i)) w=w i := by
  rw [innerMoment_centered_left,hw,mul_zero,sub_zero]
  simp [innerMoment,impulse]

/-- Sharp pair separation forced by the full-space second-order condition. -/
theorem maximum_distance_sq {z : Configuration} (hz : IsGlobalMaximum z)
    (i j : Fin 7) (hij : i≠j) : (7/18 : ℝ)≤‖z i-z j‖^2 := by
  have hc := innerMoment_cauchy (centered (impulse i)) (laplacian z (centered (impulse j)))
  rw [innerMoment_projected_impulse _ _ (laplacian_sum_zero _ _),energy_projected_impulse] at hc
  have ho := maximum_laplacian_energy hz (centered (impulse j))
  rw [energy_projected_impulse] at ho
  have hab : ‖laplacian z (centered (impulse j)) i‖^2≤(324/49 : ℝ) := by linarith
  rw [laplacian_centered,laplacian_impulse z i j hij] at hab
  simp only [norm_div,norm_neg,norm_one,norm_pow,div_pow,one_pow] at hab
  have hd : 0<‖z i-z j‖^2 := sq_pos_of_pos (norm_pos_iff.mpr
    (sub_ne_zero.mpr (fun he => hij (global_maximum_injective hz he))))
  have hh : 1≤(324/49 : ℝ)*(‖z i-z j‖^2)^2 := (div_le_iff₀ (sq_pos_of_pos hd)).mp hab
  by_contra hn
  have hlt : ‖z i-z j‖^2<(7/18 : ℝ) := lt_of_not_ge hn
  nlinarith [mul_pos (sub_pos.mpr hlt) (show (0 : ℝ)<7/18+‖z i-z j‖^2 by positivity)]

noncomputable def normalized (z : Configuration) : Configuration := scale (Real.sqrt (6/7 : ℝ)) z

theorem normalized_normSum {z : Configuration} (hz : IsGlobalMaximum z) : normSum (normalized z)=6 := by
  rw [normalized,scale_normSum,hz.1,Real.sq_sqrt (by norm_num)]
  norm_num

theorem normalized_distance (z : Configuration) (i j : Fin 7) :
    ‖normalized z i-normalized z j‖^2=(6/7 : ℝ)*‖z i-z j‖^2 := by
  simp only [normalized,scale,←mul_sub,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [Real.sq_sqrt (by norm_num)]

theorem maximum_normalized_distance {z : Configuration} (hz : IsGlobalMaximum z)
    (i j : Fin 7) (hij : i≠j) : (1/3 : ℝ)≤‖normalized z i-normalized z j‖^2 := by
  rw [normalized_distance]
  have h := maximum_distance_sq hz i j hij
  linarith

theorem realDot_sq_le (a b : ℂ) : (realDot a b)^2≤‖a‖^2*‖b‖^2 := by
  rw [norm_sq_coordinates,norm_sq_coordinates]
  simp only [realDot,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  nlinarith [sq_nonneg (a.re*b.im-a.im*b.re)]

theorem norm_sub_eq_realDot (a b : ℂ) : ‖a-b‖^2=‖a‖^2+‖b‖^2-2*realDot a b := by
  simp only [norm_sq_coordinates,Complex.sub_re,Complex.sub_im,realDot,Complex.mul_re,Complex.star_def,Complex.conj_re,Complex.conj_im]
  ring

noncomputable def pairPoint (z : Configuration) (i j : Fin 7) : Fin 3 → ℝ :=
  ![‖normalized z i‖^2,‖normalized z j‖^2,realDot (normalized z i) (normalized z j)]


theorem normalized_energy {z : Configuration} (hz : energy z=7) : energy (normalized z)=6 := by
  rw [←normSum_eq_energy,normalized,scale_normSum,normSum_eq_energy,hz,Real.sq_sqrt (by norm_num)]
  norm_num
#print axioms maximum_normalized_distance
end N7.Kernel
