import Eight.Powers

namespace MordellEight
open Finset
set_option maxHeartbeats 0

theorem radialMoment_zero (z : Configuration) : radialMoment z 0=8 := by
  norm_num [radialMoment]

theorem norm_pow_mul_real_sq (a : ℂ) (k : ℕ) (c : ℝ) :
    ‖a^k*(c : ℂ)‖^2=(‖a‖^2)^k*c^2 := by
  calc
    _ = (‖a‖^k)^2*c^2 := by
      simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
    _ = _ := by rw [←pow_mul,←pow_mul,Nat.mul_comm k 2]

theorem radialPolynomial_energy (z : Configuration) (k : ℕ) (a b : ℝ) :
    energy (fun i => (z i)^k*((a*radius z i+b : ℝ) : ℂ))=
      a^2*radialMoment z (k+2)+2*a*b*radialMoment z (k+1)+b^2*radialMoment z k := by
  rw [energy_eq_norm]
  calc
    _ = ∑ i, (a^2*(radius z i)^(k+2)+2*a*b*(radius z i)^(k+1)+b^2*(radius z i)^k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_pow_mul_real_sq]
      change (radius z i)^k*(a*radius z i+b)^2=_
      simp only [pow_add,pow_one]
      ring
    _ = _ := by simp only [radialMoment,Finset.sum_add_distrib,Finset.mul_sum]

theorem maximum_laplacian_square_energy {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z) :
    energy (laplacian z (powerConfig z 2))=49*radialMoment z 2-392 := by
  have he : laplacian z (powerConfig z 2)=(fun i => (z i)^0*((7*radius z i+(-7) : ℝ) : ℂ)) := by
    funext i
    rw [maximum_laplacian_square hz hm i]
    norm_num
    push_cast
    ring
  rw [he,radialPolynomial_energy]
  norm_num [radialMoment_one,radialMoment_zero,hz]
  ring

theorem maximum_laplacian_cube_energy {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z) :
    energy (laplacian z (powerConfig z 3))=(441/4)*radialMoment z 3-273*radialMoment z 2+1352 := by
  have he : laplacian z (powerConfig z 3)=(fun i => (z i)^1*(((21/2)*radius z i+(-13) : ℝ) : ℂ)) := by
    funext i
    rw [maximum_laplacian_cube hz hm i]
    simp only [pow_one,sub_eq_add_neg]
  rw [he,radialPolynomial_energy]
  norm_num [radialMoment_one,hz]
  ring

theorem maximum_second_moment {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z) :
    3*radialMoment z 2+‖powerSum z 2‖^2/8≤32 := by
  have h := maximum_laplacian_energy hz hm (centered (powerConfig z 2))
  rw [laplacian_centered,maximum_laplacian_square_energy hz hm,centered_power_energy] at h
  linarith

theorem maximum_third_moment {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z) :
    98*radialMoment z 3-273*radialMoment z 2+1352+(49/32)*‖powerSum z 3‖^2≤0 := by
  have h := maximum_laplacian_energy hz hm (centered (powerConfig z 3))
  rw [laplacian_centered,maximum_laplacian_cube_energy hz hm,centered_power_energy] at h
  linarith

theorem maximum_radialMoment_two {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z) :
    radialMoment z 2≤32/3 := by
  have h := maximum_second_moment hz hm
  nlinarith [sq_nonneg ‖powerSum z 2‖]

theorem radius_normalized (z : Configuration) (i : Fin 8) :
    radius (normalized z) i=(7/8 : ℝ)*radius z i := by
  simp only [radius,normalized,scale,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [Real.sq_sqrt (by norm_num)]

end MordellEight
