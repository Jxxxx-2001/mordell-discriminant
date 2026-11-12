import N6.Analysis.Normalization

set_option autoImplicit false

namespace N6
open Polynomial

/-- The real scalar used by the physical branch restrictions. -/
noncomputable def physicalScalar (w : Configuration) : ℝ := (forceParameter w)^2

/-- This theorem takes the quadratic moment as an explicit hypothesis.
The separate Newton/Vieta step deriving it from coefficient A = 1 is not assumed here. -/
theorem normSum_eq_two_add_re_sq {w : Configuration}
    (hmoment : ∑ i, (w i)^2 = (-2 : ℂ)) :
    normSum w = 2 + 2 * ∑ i, (w i).re^2 := by
  have hr : (∑ i, ((w i).re^2 - (w i).im^2)) = -2 := by
    have h := congrArg Complex.re hmoment
    norm_num [Complex.re_sum, pow_two, Complex.mul_re] at h
    simpa only [pow_two, Finset.sum_sub_distrib] using h
  calc
    normSum w = 2 * (∑ i, (w i).re^2) -
        (∑ i, ((w i).re^2 - (w i).im^2)) := by
      unfold normSum
      rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro i _
      simp only [Complex.normSq_apply]
      ring
    _ = 2 + 2 * ∑ i, (w i).re^2 := by rw [hr]; ring

theorem normSum_ge_two_of_moment {w : Configuration}
    (hmoment : ∑ i, (w i)^2 = (-2 : ℂ)) : 2 ≤ normSum w := by
  rw [normSum_eq_two_add_re_sq hmoment]
  have hs : 0 ≤ ∑ i, (w i).re^2 := Finset.sum_nonneg (fun i _ => sq_nonneg _)
  linarith

theorem all_re_zero_of_normSum_eq_two {w : Configuration}
    (hmoment : ∑ i, (w i)^2 = (-2 : ℂ)) (hq : normSum w = 2) :
    ∀ i, (w i).re = 0 := by
  have hs : (∑ i, (w i).re^2) = 0 := by
    have he := normSum_eq_two_add_re_sq hmoment
    linarith
  intro i
  have hi : (w i).re^2 ≤ ∑ j, (w j).re^2 :=
    Finset.single_le_sum (fun j _ => sq_nonneg ((w j).re)) (Finset.mem_univ i)
  have hi0 : (w i).re^2 = 0 := le_antisymm (by simpa only [hs] using hi) (sq_nonneg _)
  exact sq_eq_zero_iff.mp hi0

theorem forceParameter_le_fifteen_of_moment {w : Configuration}
    (hmoment : ∑ i, (w i)^2 = (-2 : ℂ)) : forceParameter w ≤ 15 := by
  have hq := normSum_ge_two_of_moment hmoment
  have hqpos : 0 < normSum w := by linarith
  change 30 / normSum w ≤ 15
  apply (div_le_iff₀ hqpos).mpr
  linarith

theorem physicalScalar_bounds_of_moment {w : Configuration}
    (hmoment : ∑ i, (w i)^2 = (-2 : ℂ)) :
    0 < physicalScalar w ∧ physicalScalar w ≤ 225 := by
  have hq := normSum_ge_two_of_moment hmoment
  have hk := forceParameter_pos (show 0 < normSum w by linarith)
  have hk15 := forceParameter_le_fifteen_of_moment hmoment
  constructor
  · exact sq_pos_of_pos hk
  · change (forceParameter w)^2 ≤ 225
    have he : (forceParameter w)^2 ≤ (15 : ℝ)^2 :=
      (sq_le_sq₀ (le_of_lt hk) (by norm_num)).mpr hk15
    norm_num at he ⊢
    exact he

theorem physicalScalar_endpoint_all_re_zero {w : Configuration}
    (hmoment : ∑ i, (w i)^2 = (-2 : ℂ)) (ha : physicalScalar w = 225) :
    ∀ i, (w i).re = 0 := by
  have hq := normSum_ge_two_of_moment hmoment
  have hqpos : 0 < normSum w := by linarith
  have hk := forceParameter_pos hqpos
  have hk15 : forceParameter w = 15 := by
    apply (sq_eq_sq₀ (le_of_lt hk) (by norm_num : (0 : ℝ) ≤ 15)).mp
    simpa only [physicalScalar, show (15 : ℝ)^2 = 225 by norm_num] using ha
  have he : (30 : ℝ) = 15 * normSum w := by
    apply (div_eq_iff (ne_of_gt hqpos)).mp
    exact hk15
  apply all_re_zero_of_normSum_eq_two hmoment
  linarith

/-- Purely imaginary roots identify conjugation with scaling all six roots by -1. -/
theorem rootPolynomial_map_conj_of_all_re_zero {w : Configuration}
    (hw : ∀ i, (w i).re = 0) :
    (rootPolynomial w).map (starRingEnd ℂ) =
      rootPolynomial (scaleConfiguration (-1) w) := by
  have hc (i : Fin 6) : (starRingEnd ℂ) (w i) = -w i := by
    apply Complex.ext <;> simp [hw i]
  unfold rootPolynomial
  rw [Polynomial.map_prod]
  apply Finset.prod_congr rfl
  intro i _
  simp only [Polynomial.map_sub, Polynomial.map_X, Polynomial.map_C,
    scaleConfiguration, hc i, neg_one_mul]

theorem rootPolynomial_coeff_three_conj_of_all_re_zero {w : Configuration}
    (hw : ∀ i, (w i).re = 0) :
    (starRingEnd ℂ) ((rootPolynomial w).coeff 3) = -(rootPolynomial w).coeff 3 := by
  have hc := congrArg (fun p : ℂ[X] => p.coeff 3)
    (rootPolynomial_map_conj_of_all_re_zero hw)
  dsimp only at hc
  rw [coeff_map, rootPolynomial_scale_coeff] at hc
  norm_num at hc
  exact hc

theorem rootPolynomial_coeff_three_re_zero {w : Configuration}
    (hw : ∀ i, (w i).re = 0) : ((rootPolynomial w).coeff 3).re = 0 := by
  have hr := congrArg Complex.re (rootPolynomial_coeff_three_conj_of_all_re_zero hw)
  simp only [Complex.conj_re, Complex.neg_re] at hr
  linarith

/-- The odd coefficient is purely imaginary, so its square is real and nonpositive. -/
theorem rootPolynomial_coeff_three_square_physical {w : Configuration}
    (hw : ∀ i, (w i).re = 0) :
    (((rootPolynomial w).coeff 3)^2).im = 0 ∧
      (((rootPolynomial w).coeff 3)^2).re ≤ 0 := by
  have hb := rootPolynomial_coeff_three_re_zero hw
  constructor
  · simp [pow_two, Complex.mul_im, hb]
  · simp only [pow_two, Complex.mul_re, hb, zero_mul, zero_sub]
    exact neg_nonpos.mpr (mul_self_nonneg _)

theorem physicalScalar_endpoint_coeff_three_square {w : Configuration}
    (hmoment : ∑ i, (w i)^2 = (-2 : ℂ)) (ha : physicalScalar w = 225) :
    (((rootPolynomial w).coeff 3)^2).im = 0 ∧
      (((rootPolynomial w).coeff 3)^2).re ≤ 0 :=
  rootPolynomial_coeff_three_square_physical (physicalScalar_endpoint_all_re_zero hmoment ha)

end N6
