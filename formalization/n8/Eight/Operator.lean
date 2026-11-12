import Eight.Pairs

namespace MordellEight
open Finset
set_option maxHeartbeats 0

theorem pair_polarization (z v w : Configuration) :
    pairQuadratic z (v+w)-pairQuadratic z (v-w)=4*pairBilinear z v w := by
  unfold pairQuadratic pairBilinear
  simp only [div_pow]
  rw [←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

theorem energy_parallelogram (v w : Configuration) :
    energy (v+w)+energy (v-w)=2*energy v+2*energy w := by
  calc
    _ = ∑ i, (‖(v+w) i‖^2+‖(v-w) i‖^2) := by
      simp only [energy_eq_norm,Finset.sum_add_distrib]
    _ = ∑ i, (2*‖v i‖^2+2*‖w i‖^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Pi.add_apply,Pi.sub_apply,norm_sq_coordinates,
        Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
      ring
    _ = _ := by simp only [energy_eq_norm,Finset.sum_add_distrib,Finset.mul_sum]

theorem maximum_pairBilinear_re_upper {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z)
    (v w : Configuration) : (pairBilinear z v w).re≤(7/4)*(energy v+energy w) := by
  have hp := (maximum_pairQuadratic_re_bounds hz hm (v+w)).2
  have hn := (maximum_pairQuadratic_re_bounds hz hm (v-w)).1
  have hpol : (pairQuadratic z (v+w)).re-(pairQuadratic z (v-w)).re=
      4*(pairBilinear z v w).re := by
    simpa using congrArg Complex.re (pair_polarization z v w)
  have he := energy_parallelogram v w
  linarith

noncomputable def laplacianDual (z w : Configuration) : Configuration :=
  fun i => star (laplacian z w i)/(7/2)

theorem pairBilinear_dual (z w : Configuration) :
    (pairBilinear z (laplacianDual z w) w).re=energy (laplacian z w)/(7/2) := by
  rw [pairBilinear_laplacian,Complex.re_sum]
  simp only [energy_eq_norm]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [laplacianDual]
  simp only [Complex.mul_re,Complex.div_re,Complex.div_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,norm_sq_coordinates]
  norm_num
  ring

theorem laplacianDual_energy (z w : Configuration) :
    energy (laplacianDual z w)=energy (laplacian z w)/(49/4) := by
  simp only [energy_eq_norm,laplacianDual,norm_div,norm_star,div_pow]
  norm_num
  rw [Finset.sum_div]

/-- The exact l2 operator bound, expressed with energy so the Pi sup norm cannot enter. -/
theorem maximum_laplacian_energy {z : Configuration} (hz : energy z=8)
    (hm : ∀ y : Configuration, energy y=8 → delta y≤delta z)
    (w : Configuration) : energy (laplacian z w)≤(49/4)*energy w := by
  have h := maximum_pairBilinear_re_upper hz hm (laplacianDual z w) w
  rw [pairBilinear_dual,laplacianDual_energy] at h
  linarith

theorem innerMoment_cauchy (v w : Configuration) : ‖innerMoment v w‖^2≤energy v*energy w := by
  have hn : ‖innerMoment v w‖≤∑ i, ‖v i‖*‖w i‖ := by
    unfold innerMoment
    calc
      _ ≤ ∑ i, ‖star (v i)*w i‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul,norm_star]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin 8 => ‖v i‖)
    (fun i : Fin 8 => ‖w i‖)
  have hs : 0≤∑ i, ‖v i‖*‖w i‖ := Finset.sum_nonneg (fun i _ => by positivity)
  rw [←energy_eq_norm v,←energy_eq_norm w] at hc
  nlinarith [norm_nonneg (innerMoment v w)]

end MordellEight
