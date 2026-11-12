import N7.Analysis.Definitions
import Mathlib.RingTheory.Polynomial.ScaleRoots

set_option autoImplicit false

namespace N7.Analysis

noncomputable def forceParameter (w : Configuration) : ℝ := 42 / normSum w
noncomputable def physicalScalar (w : Configuration) : ℝ := (forceParameter w)^2

theorem forceParameter_pos {w : Configuration} (hq : 0 < normSum w) :
    0 < forceParameter w := div_pos (by norm_num) hq

/-- An explicit moment hypothesis: no coefficient/resultant bridge is assumed. -/
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

theorem forceParameter_le_twentyone_of_moment {w : Configuration}
    (hmoment : ∑ i, (w i)^2 = (-2 : ℂ)) : forceParameter w ≤ 21 := by
  have hq := normSum_ge_two_of_moment hmoment
  have hqpos : 0 < normSum w := by linarith
  change 42 / normSum w ≤ 21
  apply (div_le_iff₀ hqpos).mpr
  linarith

theorem physicalScalar_bounds_of_moment {w : Configuration}
    (hmoment : ∑ i, (w i)^2 = (-2 : ℂ)) :
    0 < physicalScalar w ∧ physicalScalar w ≤ 441 := by
  have hq := normSum_ge_two_of_moment hmoment
  have hk := forceParameter_pos (show 0 < normSum w by linarith)
  have hk21 := forceParameter_le_twentyone_of_moment hmoment
  constructor
  · exact sq_pos_of_pos hk
  · change (forceParameter w)^2 ≤ 441
    have he : (forceParameter w)^2 ≤ (21 : ℝ)^2 :=
      (sq_le_sq₀ (le_of_lt hk) (by norm_num)).mpr hk21
    norm_num at he ⊢
    exact he

theorem physicalScalar_endpoint_all_re_zero {w : Configuration}
    (hmoment : ∑ i, (w i)^2 = (-2 : ℂ)) (ha : physicalScalar w = 441) :
    ∀ i, (w i).re = 0 := by
  have hq := normSum_ge_two_of_moment hmoment
  have hqpos : 0 < normSum w := by linarith
  have hk := forceParameter_pos hqpos
  have hk21 : forceParameter w = 21 := by
    apply (sq_eq_sq₀ (le_of_lt hk) (by norm_num : (0 : ℝ) ≤ 21)).mp
    simpa only [physicalScalar, show (21 : ℝ)^2 = 441 by norm_num] using ha
  have he : (42 : ℝ) = 21 * normSum w := by
    apply (div_eq_iff (ne_of_gt hqpos)).mp
    exact hk21
  apply all_re_zero_of_normSum_eq_two hmoment
  linarith

open Polynomial

/-- A reusable root-product interface, independent of any resultant. -/
noncomputable def rootProduct {n : ℕ} (w : Fin n → ℂ) : ℂ[X] :=
  ∏ i, (X - C (w i))

theorem rootProduct_natDegree {n : ℕ} (w : Fin n → ℂ) :
    (rootProduct w).natDegree = n := by
  unfold rootProduct
  rw [natDegree_prod_of_monic (Finset.univ : Finset (Fin n))
    (fun i => X - C (w i)) (fun i _ => monic_X_sub_C (w i))]
  simp

theorem rootProduct_map_conj {n : ℕ} (w : Fin n → ℂ) :
    (rootProduct w).map (starRingEnd ℂ) =
      rootProduct (fun i => (starRingEnd ℂ) (w i)) := by
  simp only [rootProduct, Polynomial.map_prod, Polynomial.map_sub,
    Polynomial.map_X, Polynomial.map_C]

theorem rootProduct_scale {n : ℕ} (w : Fin n → ℂ) (α : ℂ) :
    rootProduct (fun i => α * w i) = (rootProduct w).scaleRoots α := by
  unfold rootProduct
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      mul_scaleRoots_of_noZeroDivisors, X_sub_C_scaleRoots, ih]
    simp only [mul_comm (w a) α]

theorem rootProduct_scale_coeff {n : ℕ} (w : Fin n → ℂ) (α : ℂ) (j : ℕ) :
    (rootProduct (fun i => α * w i)).coeff j =
      (rootProduct w).coeff j * α^(n-j) := by
  rw [rootProduct_scale, coeff_scaleRoots, rootProduct_natDegree]

theorem rootProduct_coeff_five_pair_products (w : Configuration) :
    (rootProduct w).coeff 5 =
      w 0*w 1 + w 0*w 2 + w 0*w 3 + w 0*w 4 + w 0*w 5 + w 0*w 6 +
      w 1*w 2 + w 1*w 3 + w 1*w 4 + w 1*w 5 + w 1*w 6 +
      w 2*w 3 + w 2*w 4 + w 2*w 5 + w 2*w 6 +
      w 3*w 4 + w 3*w 5 + w 3*w 6 + w 4*w 5 + w 4*w 6 + w 5*w 6 := by
  simp [rootProduct, Fin.prod_univ_succ, sub_mul,
    coeff_sub, coeff_X_mul, coeff_C_mul, coeff_X]
  ring

theorem rootProduct_secondMoment (w : Configuration) :
    (2 : ℂ) * (rootProduct w).coeff 5 = (∑ i, w i)^2 - ∑ i, (w i)^2 := by
  rw [rootProduct_coeff_five_pair_products, sum_expand w, sum_expand (fun i => (w i)^2)]
  ring

theorem secondMoment_eq_neg_two_of_centered_normalized {w : Configuration}
    (hcenter : ∑ i, w i = 0) (hA : (rootProduct w).coeff 5 = 1) :
    ∑ i, (w i)^2 = (-2 : ℂ) := by
  have h := rootProduct_secondMoment w
  rw [hcenter, hA] at h
  linear_combination h

theorem physicalScalar_bounds_of_centered_normalized {w : Configuration}
    (hcenter : ∑ i, w i = 0) (hA : (rootProduct w).coeff 5 = 1) :
    0 < physicalScalar w ∧ physicalScalar w ≤ 441 :=
  physicalScalar_bounds_of_moment (secondMoment_eq_neg_two_of_centered_normalized hcenter hA)

/-- The mixed cubic coefficient is physical because the dual roots are conjugate
roots scaled by a positive real scalar. The separate resultant identity is absent. -/
theorem physical_mixed_coefficient {w : Configuration} (κ : ℝ) (hκ : 0 ≤ κ) :
    let b := (rootProduct w).coeff 4
    let r := (rootProduct (fun i => (κ : ℂ) * (starRingEnd ℂ) (w i))).coeff 4
    (b * r).im = 0 ∧ 0 ≤ (b * r).re := by
  dsimp only
  rw [rootProduct_scale_coeff, ← rootProduct_map_conj, coeff_map]
  have he (b : ℂ) : b * ((starRingEnd ℂ) b * (κ : ℂ)^3) =
      ((κ^3 * Complex.normSq b : ℝ) : ℂ) := by
    rw [Complex.ofReal_mul, Complex.ofReal_pow, Complex.normSq_eq_conj_mul_self]
    ring
  rw [he]
  simp only [Complex.ofReal_im, Complex.ofReal_re, true_and]
  exact mul_nonneg (pow_nonneg hκ _) (Complex.normSq_nonneg _)

#print axioms physicalScalar_bounds_of_moment
#print axioms physicalScalar_bounds_of_centered_normalized
#print axioms physicalScalar_endpoint_all_re_zero
#print axioms physical_mixed_coefficient

end N7.Analysis
