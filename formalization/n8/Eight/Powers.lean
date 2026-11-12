import Eight.Distance

namespace MordellEight
open Finset
set_option maxHeartbeats 0

noncomputable def radius (z : Configuration) (i : Fin 8) : ℝ := ‖z i‖^2
def powerConfig (z : Configuration) (k : ℕ) : Configuration := fun i => (z i)^k
noncomputable def powerSum (z : Configuration) (k : ℕ) : ℂ := ∑ i, (z i)^k
noncomputable def radialMoment (z : Configuration) (k : ℕ) : ℝ := ∑ i, (radius z i)^k

theorem radialMoment_one (z : Configuration) : radialMoment z 1=energy z := by
  simp only [radialMoment,pow_one,radius,energy_eq_norm]

theorem powerConfig_energy (z : Configuration) (k : ℕ) : energy (powerConfig z k)=radialMoment z k := by
  rw [energy_eq_norm]
  unfold powerConfig radialMoment radius
  apply Finset.sum_congr rfl
  intro i hi
  rw [norm_pow,←pow_mul,←pow_mul,Nat.mul_comm k 2]

theorem centroid_eq_sum_div (z : Configuration) : centroid z=(∑ i,z i)/8 := by
  have h := sum_eq_eight_centroid z
  rw [h]
  ring

theorem centered_power_energy (z : Configuration) (k : ℕ) :
    energy (centered (powerConfig z k))=radialMoment z k-‖powerSum z k‖^2/8 := by
  rw [centered_energy,powerConfig_energy,centroid_eq_sum_div]
  change radialMoment z k-8*‖powerSum z k/8‖^2=_
  simp only [norm_div,div_pow]
  norm_num
  ring

theorem sum_erase_eq_sub {A : Type*} [AddCommGroup A] (f : Fin 8 → A) (i : Fin 8) :
    (∑ j ∈ Finset.univ.erase i, f j)=(∑ j,f j)-f i :=
  eq_sub_of_add_eq (Finset.sum_erase_add _ _ (Finset.mem_univ i))

theorem laplacian_eq_erase (z w : Configuration) (i : Fin 8) :
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

theorem maximum_laplacian_square {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z) (i : Fin 8) :
    laplacian z (powerConfig z 2) i=((7*(radius z i-1) : ℝ) : ℂ) := by
  have hi := maximum_injective hm
  have he : ∀ j ∈ Finset.univ.erase i, z i-z j≠0 := by
    intro j hj
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 (hi h).symm)
  calc
    _ = ∑ j ∈ Finset.univ.erase i, (2*z i*(z i-z j)⁻¹-1) := by
      rw [laplacian_eq_erase]
      exact Finset.sum_congr rfl (fun j hj => second_difference _ _ (he j hj))
    _ = 2*z i*(∑ j ∈ Finset.univ.erase i,(z i-z j)⁻¹)-7 := by
      rw [Finset.sum_sub_distrib,←Finset.mul_sum]
      norm_num
    _ = 7*(z i*star (z i)-1) := by rw [maximum_force hz hm i]; ring
    _ = _ := by rw [mul_star_norm_sq]; unfold radius; push_cast; rfl

theorem maximum_laplacian_cube {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z) (i : Fin 8) :
    laplacian z (powerConfig z 3) i=z i*(((21/2)*radius z i-13 : ℝ) : ℂ) := by
  have hi := maximum_injective hm
  have he : ∀ j ∈ Finset.univ.erase i, z i-z j≠0 := by
    intro j hj
    exact sub_ne_zero.mpr (fun h => (Finset.mem_erase.mp hj).1 (hi h).symm)
  calc
    _ = ∑ j ∈ Finset.univ.erase i, (3*(z i)^2*(z i-z j)⁻¹-2*z i-z j) := by
      rw [laplacian_eq_erase]
      exact Finset.sum_congr rfl (fun j hj => third_difference _ _ (he j hj))
    _ = 3*(z i)^2*(∑ j ∈ Finset.univ.erase i,(z i-z j)⁻¹)-14*z i-
        ((∑ j,z j)-z i) := by
      simp only [Finset.sum_sub_distrib,←Finset.mul_sum,Finset.sum_const,
        Finset.card_erase_of_mem (Finset.mem_univ i),Finset.card_univ,Fintype.card_fin,nsmul_eq_mul,
        sum_erase_eq_sub]
      norm_num <;> ring
    _ = z i*((21/2)*(z i*star (z i))-13) := by
      rw [maximum_force hz hm i,maximum_sum_zero hz hm]
      ring
    _ = _ := by rw [mul_star_norm_sq]; unfold radius; push_cast; rfl

end MordellEight
