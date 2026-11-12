import N7.Analysis.SecondVariation
import N7.Analysis.Force

set_option autoImplicit false
set_option maxHeartbeats 1200000
namespace N7.Kernel
open N7.Analysis Finset

theorem energy_eq_norm (z : Configuration) : energy z = ∑ i, ‖z i‖^2 := rfl

theorem normSum_eq_norm (z : Configuration) : normSum z = ∑ i, ‖z i‖^2 := by
  simp only [normSum,Complex.normSq_eq_norm_sq]

theorem norm_sq_coordinates (z : ℂ) : ‖z‖^2 = z.re^2+z.im^2 := by
  rw [Complex.sq_norm,Complex.normSq_apply]
  ring

theorem innerMoment_self (z : Configuration) : innerMoment z z = (normSum z : ℂ) := by
  simp only [innerMoment,normSum,Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.star_def,mul_comm,Complex.mul_conj]

theorem innerMoment_shift (z w : Configuration) (a : ℝ) :
    innerMoment z (fun i => w i-(a:ℂ)*z i) = innerMoment z w-(a:ℂ)*(normSum z:ℂ) := by
  simp only [innerMoment,mul_sub,Finset.sum_sub_distrib]
  rw [show (∑ i,star (z i)*((a:ℂ)*z i))=(a:ℂ)*innerMoment z z by
    simp only [innerMoment,Finset.mul_sum]; apply Finset.sum_congr rfl; intro i _; ring]
  rw [innerMoment_self]

theorem normSum_shift (z w : Configuration) (a : ℝ) :
    normSum (fun i => w i-(a:ℂ)*z i)=
      normSum w-2*a*(innerMoment z w).re+a^2*normSum z := by
  calc
    _ = ∑ i, (Complex.normSq (w i)-2*a*(star (z i)*w i).re+a^2*Complex.normSq (z i)) := by
      apply Finset.sum_congr rfl
      intro i _
      simp [Complex.normSq_apply,Complex.mul_re,Complex.mul_im,Complex.star_def]
      ring
    _ = _ := by simp only [normSum,innerMoment,Complex.re_sum,Finset.sum_add_distrib,
      Finset.sum_sub_distrib,Finset.mul_sum]

theorem pairSquareSum_shift {z : Configuration} (hz : IsGlobalMaximum z)
    (w : Configuration) (a : ℝ) :
    pairSquareSum z (fun i => w i-(a:ℂ)*z i)=
      pairSquareSum z w-2*(a:ℂ)*pairSum z w+21*(a:ℂ)^2 := by
  calc
    _ = ∑ p ∈ pairs, (((w p.1-w p.2)/(z p.1-z p.2))^2-
        2*(a:ℂ)*((w p.1-w p.2)/(z p.1-z p.2))+(a:ℂ)^2) := by
      apply Finset.sum_congr rfl
      intro p hp
      have hd := global_maximum_sub_ne_zero hz (ne_of_lt (Finset.mem_filter.mp hp).2)
      field_simp
      <;> ring
    _ = _ := by
      simp only [pairSquareSum,pairSum,Finset.sum_add_distrib,Finset.sum_sub_distrib,
        ←Finset.mul_sum,Finset.sum_const,pairs_card,nsmul_eq_mul,Nat.cast_ofNat]

theorem pairSquareSum_scale (z w : Configuration) (c : ℂ) :
    pairSquareSum z (fun i => c*w i)=c^2*pairSquareSum z w := by
  simp only [pairSquareSum,←mul_sub,mul_div_assoc,mul_pow,Finset.mul_sum]

theorem maximum_pairQuadratic_lower {z : Configuration} (hz : IsGlobalMaximum z)
    (w : Configuration) : -3*normSum w ≤ (pairSquareSum z w).re := by
  let a : ℝ := (innerMoment z w).re/7
  have ht : (innerMoment z (fun i => w i-(a:ℂ)*z i)).re=0 := by
    rw [innerMoment_shift,hz.1]
    simp [a]
    <;> ring
  have h := global_maximum_second_variation hz _ ht
  rw [normSum_shift,pairSquareSum_shift hz,hz.1] at h
  have hfirst := global_maximum_pairSum_real hz w
  norm_num [pow_two,Complex.mul_re,Complex.mul_im] at h
  have hp : (pairSum z w).re = 3*(innerMoment z w).re := by linarith
  rw [hp] at h
  dsimp [a] at h
  nlinarith [sq_nonneg (innerMoment z w).re]

theorem maximum_pairQuadratic_re_bounds {z : Configuration} (hz : IsGlobalMaximum z)
    (w : Configuration) : -3*normSum w ≤ (pairSquareSum z w).re ∧
      (pairSquareSum z w).re ≤ 3*normSum w := by
  have hI := maximum_pairQuadratic_lower hz (fun i => Complex.I*w i)
  rw [pairSquareSum_scale,normSum_scale] at hI
  norm_num at hI
  exact ⟨maximum_pairQuadratic_lower hz w,by linarith⟩

#print axioms maximum_pairQuadratic_re_bounds
end N7.Kernel
