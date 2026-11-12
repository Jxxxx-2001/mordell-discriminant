import N7.Kernel.MaximumGeometry
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace N7.Kernel
open Finset N7.Analysis

theorem maximum_force {z : Configuration} (hz : IsGlobalMaximum z) (i : Fin 7) :
    (∑ j ∈ Finset.univ.erase i, (z i-z j)⁻¹) = (3:ℂ)*star (z i) := by
  simpa only [one_div,Complex.star_def] using global_maximum_force_sum hz i

theorem maximum_sum_zero {z : Configuration} (hz : IsGlobalMaximum z) : (∑ i,z i)=0 :=
  global_maximum_centered hz

noncomputable def radius (z : Configuration) (i : Fin 7) : ℝ := ‖z i‖^2
def powerConfig (z : Configuration) (k : ℕ) : Configuration := fun i => (z i)^k
noncomputable def powerSum (z : Configuration) (k : ℕ) : ℂ := ∑ i, (z i)^k
noncomputable def radialMoment (z : Configuration) (k : ℕ) : ℝ := ∑ i, (radius z i)^k

theorem radialMoment_one (z : Configuration) : radialMoment z 1=normSum z := by
  simp only [radialMoment,pow_one,radius,normSum_eq_norm]

theorem powerConfig_energy (z : Configuration) (k : ℕ) : normSum (powerConfig z k)=radialMoment z k := by
  rw [normSum_eq_norm]
  unfold powerConfig radialMoment radius
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_pow,←pow_mul,←pow_mul,Nat.mul_comm k 2]

theorem centroid_eq_sum_div (z : Configuration) : centroid z=(∑ i,z i)/7 := rfl

theorem centered_power_energy (z : Configuration) (k : ℕ) :
    normSum (centered (powerConfig z k))=radialMoment z k-‖powerSum z k‖^2/7 := by
  rw [centered_normSum,powerConfig_energy,centroid_eq_sum_div]
  change radialMoment z k-7*‖powerSum z k/7‖^2=_
  simp only [norm_div,div_pow]
  norm_num
  ring

theorem sum_erase_eq_sub {A : Type*} [AddCommGroup A] (f : Fin 7 → A) (i : Fin 7) :
    (∑ j ∈ Finset.univ.erase i, f j)=(∑ j,f j)-f i :=
  eq_sub_of_add_eq (Finset.sum_erase_add _ _ (Finset.mem_univ i))

theorem laplacian_eq_erase (z w : Configuration) (i : Fin 7) :
    laplacian z w i=∑ j ∈ Finset.univ.erase i, (w i-w j)/(z i-z j)^2 := by
  rw [laplacian,←Finset.sum_erase_add _ _ (Finset.mem_univ i)]
  simp

theorem mul_star_norm_sq (a : ℂ) : a*star a=((‖a‖^2 : ℝ) : ℂ) := by
  rw [Complex.star_def,Complex.mul_conj,Complex.sq_norm]

theorem second_difference (a b : ℂ) (h : a-b≠0) :
    (a^2-b^2)/(a-b)^2=2*a*(a-b)⁻¹-1 := by field_simp; ring

theorem third_difference (a b : ℂ) (h : a-b≠0) :
    (a^3-b^3)/(a-b)^2=3*a^2*(a-b)⁻¹-2*a-b := by field_simp; ring

theorem fourth_difference (a b : ℂ) (h : a-b≠0) :
    (a^4-b^4)/(a-b)^2=4*a^3*(a-b)⁻¹-3*a^2-2*a*b-b^2 := by field_simp; ring

theorem maximum_laplacian_square {z : Configuration} (hz : IsGlobalMaximum z) (i : Fin 7) :
    laplacian z (powerConfig z 2) i=((6*(radius z i-1) : ℝ) : ℂ) := by
  have hi := global_maximum_injective hz
  have he : ∀ j ∈ Finset.univ.erase i, z i-z j≠0 := by
    intro j hj
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 (hi h).symm)
  calc
    _ = ∑ j ∈ Finset.univ.erase i, (2*z i*(z i-z j)⁻¹-1) := by
      rw [laplacian_eq_erase]
      exact Finset.sum_congr rfl (fun j hj => second_difference _ _ (he j hj))
    _ = 2*z i*(∑ j ∈ Finset.univ.erase i,(z i-z j)⁻¹)-6 := by
      rw [Finset.sum_sub_distrib,←Finset.mul_sum]
      norm_num
    _ = 6*(z i*star (z i)-1) := by rw [maximum_force hz i]; ring
    _ = _ := by rw [mul_star_norm_sq]; unfold radius; push_cast; rfl

theorem maximum_laplacian_cube {z : Configuration} (hz : IsGlobalMaximum z) (i : Fin 7) :
    laplacian z (powerConfig z 3) i=z i*((9*radius z i-11 : ℝ) : ℂ) := by
  have hi := global_maximum_injective hz
  have he : ∀ j ∈ Finset.univ.erase i, z i-z j≠0 := by
    intro j hj
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 (hi h).symm)
  calc
    _ = ∑ j ∈ Finset.univ.erase i, (3*(z i)^2*(z i-z j)⁻¹-2*z i-z j) := by
      rw [laplacian_eq_erase]
      exact Finset.sum_congr rfl (fun j hj => third_difference _ _ (he j hj))
    _ = 3*(z i)^2*(∑ j ∈ Finset.univ.erase i,(z i-z j)⁻¹)-12*z i-
        ((∑ j,z j)-z i) := by
      simp only [Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        sum_erase_eq_sub]
      norm_num <;> ring
    _ = z i*(9*(z i*star (z i))-11) := by
      rw [maximum_force hz i,maximum_sum_zero hz]
      ring
    _ = _ := by rw [mul_star_norm_sq]; unfold radius; push_cast; rfl

theorem radialMoment_zero (z : Configuration) : radialMoment z 0=7 := by
  norm_num [radialMoment]

theorem norm_pow_mul_real_sq (a : ℂ) (k : ℕ) (c : ℝ) :
    ‖a^k*(c : ℂ)‖^2=(‖a‖^2)^k*c^2 := by
  calc
    _ = (‖a‖^k)^2*c^2 := by
      simp only [norm_mul,norm_pow,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
    _ = _ := by rw [←pow_mul,←pow_mul,Nat.mul_comm k 2]

theorem radialPolynomial_energy (z : Configuration) (k : ℕ) (a b : ℝ) :
    normSum (fun i => (z i)^k*((a*radius z i+b : ℝ) : ℂ))=
      a^2*radialMoment z (k+2)+2*a*b*radialMoment z (k+1)+b^2*radialMoment z k := by
  rw [normSum_eq_norm]
  calc
    _ = ∑ i, (a^2*(radius z i)^(k+2)+2*a*b*(radius z i)^(k+1)+b^2*(radius z i)^k) := by
      apply Finset.sum_congr rfl
      intro i hi
      rw [norm_pow_mul_real_sq]
      change (radius z i)^k*(a*radius z i+b)^2=_
      simp only [pow_add,pow_one]
      ring
    _ = _ := by simp only [radialMoment,Finset.sum_add_distrib,Finset.mul_sum]

theorem maximum_laplacian_square_energy {z : Configuration} (hz : IsGlobalMaximum z) :
    normSum (laplacian z (powerConfig z 2))=36*radialMoment z 2-252 := by
  have he : laplacian z (powerConfig z 2)=(fun i => (z i)^0*((6*radius z i+(-6) : ℝ) : ℂ)) := by
    funext i
    rw [maximum_laplacian_square hz i]
    norm_num
    push_cast
    ring
  rw [he,radialPolynomial_energy]
  norm_num [radialMoment_one,radialMoment_zero,hz.1]
  ring

theorem maximum_laplacian_cube_energy {z : Configuration} (hz : IsGlobalMaximum z) :
    normSum (laplacian z (powerConfig z 3))=81*radialMoment z 3-198*radialMoment z 2+847 := by
  have he : laplacian z (powerConfig z 3)=(fun i => (z i)^1*((9*radius z i+(-11) : ℝ) : ℂ)) := by
    funext i
    rw [maximum_laplacian_cube hz i]
    simp only [pow_one,sub_eq_add_neg]
  rw [he,radialPolynomial_energy]
  norm_num [radialMoment_one,hz.1]
  ring

theorem maximum_second_moment {z : Configuration} (hz : IsGlobalMaximum z) :
    3*radialMoment z 2+‖powerSum z 2‖^2/7≤28 := by
  have h := maximum_laplacian_energy hz (centered (powerConfig z 2))
  rw [laplacian_centered,maximum_laplacian_square_energy hz,centered_power_energy] at h
  linarith

theorem maximum_third_moment {z : Configuration} (hz : IsGlobalMaximum z) :
    72*radialMoment z 3-198*radialMoment z 2+847+(9/7)*‖powerSum z 3‖^2≤0 := by
  have h := maximum_laplacian_energy hz (centered (powerConfig z 3))
  rw [laplacian_centered,maximum_laplacian_cube_energy hz,centered_power_energy] at h
  linarith

theorem maximum_radialMoment_two {z : Configuration} (hz : IsGlobalMaximum z) :
    radialMoment z 2≤28/3 := by
  have h := maximum_second_moment hz
  nlinarith [sq_nonneg ‖powerSum z 2‖]

theorem radius_normalized (z : Configuration) (i : Fin 7) :
    radius (normalized z) i=(6/7 : ℝ)*radius z i := by
  simp only [radius,normalized,scale,norm_mul,Complex.norm_real,Real.norm_eq_abs,mul_pow,sq_abs]
  rw [Real.sq_sqrt (by norm_num)]


#print axioms maximum_second_moment
#print axioms maximum_third_moment
end N7.Kernel
