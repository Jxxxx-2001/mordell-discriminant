import N7.Kernel.MaximumQuadratic
import N7.Kernel.Pairs
set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace N7.Kernel
open Finset N7.Analysis
noncomputable def laplacian (z w : Configuration) : Configuration :=
  fun i => ∑ j, (w i-w j)/(z i-z j)^2

noncomputable def pairBilinear (z v w : Configuration) : ℂ :=
  ∑ ij ∈ pairs, (v ij.1-v ij.2)*(w ij.1-w ij.2)/(z ij.1-z ij.2)^2

theorem pairBilinear_self (z w : Configuration) : pairBilinear z w w=pairSquareSum z w := by
  unfold pairBilinear pairSquareSum
  apply Finset.sum_congr rfl
  intro ij hij
  rw [div_pow,pow_two (w ij.1-w ij.2)]

theorem pairBilinear_laplacian (z v w : Configuration) :
    pairBilinear z v w=∑ i, v i*laplacian z w i := by
  symm
  unfold laplacian
  simp only [Finset.mul_sum,←mul_div_assoc]
  rw [double_sum_pairs (fun i j => v i*(w i-w j)/(z i-z j)^2) (by intro i; simp)]
  unfold pairBilinear
  apply Finset.sum_congr rfl
  intro ij hij
  rw [show z ij.2-z ij.1=-(z ij.1-z ij.2) by ring,neg_sq]
  ring


theorem pair_polarization (z v w : Configuration) :
    pairSquareSum z (v+w)-pairSquareSum z (v-w)=4*pairBilinear z v w := by
  unfold pairSquareSum pairBilinear
  simp only [div_pow]
  rw [←Finset.sum_sub_distrib,Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  simp only [Pi.add_apply,Pi.sub_apply]
  ring

theorem energy_parallelogram (v w : Configuration) :
    normSum (v+w)+normSum (v-w)=2*normSum v+2*normSum w := by
  calc
    _ = ∑ i, (‖(v+w) i‖^2+‖(v-w) i‖^2) := by
      simp only [normSum_eq_norm,Finset.sum_add_distrib]
    _ = ∑ i, (2*‖v i‖^2+2*‖w i‖^2) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [Pi.add_apply,Pi.sub_apply,norm_sq_coordinates,
        Complex.add_re,Complex.add_im,Complex.sub_re,Complex.sub_im]
      ring
    _ = _ := by simp only [normSum_eq_norm,Finset.sum_add_distrib,Finset.mul_sum]

theorem maximum_pairBilinear_re_upper {z : Configuration} (hz : IsGlobalMaximum z)
    (v w : Configuration) : (pairBilinear z v w).re≤(3/2)*(normSum v+normSum w) := by
  have hp := (maximum_pairQuadratic_re_bounds hz (v+w)).2
  have hn := (maximum_pairQuadratic_re_bounds hz (v-w)).1
  have hpol : (pairSquareSum z (v+w)).re-(pairSquareSum z (v-w)).re=
      4*(pairBilinear z v w).re := by
    simpa using congrArg Complex.re (pair_polarization z v w)
  have he := energy_parallelogram v w
  linarith

noncomputable def laplacianDual (z w : Configuration) : Configuration :=
  fun i => star (laplacian z w i)/3

theorem pairBilinear_dual (z w : Configuration) :
    (pairBilinear z (laplacianDual z w) w).re=normSum (laplacian z w)/3 := by
  rw [pairBilinear_laplacian,Complex.re_sum]
  simp only [normSum_eq_norm]
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro i hi
  dsimp [laplacianDual]
  simp only [Complex.mul_re,Complex.div_re,Complex.div_im,Complex.star_def,
    Complex.conj_re,Complex.conj_im,norm_sq_coordinates]
  norm_num
  ring

theorem laplacianDual_energy (z w : Configuration) :
    normSum (laplacianDual z w)=normSum (laplacian z w)/9 := by
  simp only [normSum_eq_norm,laplacianDual,norm_div,norm_star,div_pow]
  norm_num
  rw [Finset.sum_div]

/-- The exact l2 operator bound, expressed with normSum so the Pi sup norm cannot enter. -/
theorem maximum_laplacian_energy {z : Configuration} (hz : IsGlobalMaximum z)
    (w : Configuration) : normSum (laplacian z w)≤9*normSum w := by
  have h := maximum_pairBilinear_re_upper hz (laplacianDual z w) w
  rw [pairBilinear_dual,laplacianDual_energy] at h
  linarith

theorem innerMoment_cauchy (v w : Configuration) : ‖innerMoment v w‖^2≤normSum v*normSum w := by
  have hn : ‖innerMoment v w‖≤∑ i, ‖v i‖*‖w i‖ := by
    unfold innerMoment
    calc
      _ ≤ ∑ i, ‖star (v i)*w i‖ := norm_sum_le _ _
      _ = _ := by simp only [norm_mul,norm_star]
  have hc := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i : Fin 7 => ‖v i‖)
    (fun i : Fin 7 => ‖w i‖)
  have hs : 0≤∑ i, ‖v i‖*‖w i‖ := Finset.sum_nonneg (fun i _ => by positivity)
  rw [←normSum_eq_norm v,←normSum_eq_norm w] at hc
  nlinarith [norm_nonneg (innerMoment v w)]


#print axioms maximum_laplacian_energy
end N7.Kernel
