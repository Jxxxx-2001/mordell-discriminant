import N7.Analysis.Directional
import Mathlib.Analysis.Calculus.Deriv.Polynomial
import Mathlib.Algebra.Polynomial.Inductions

set_option autoImplicit false

namespace N7.Analysis

open Polynomial Filter
open scoped Topology

private theorem second_coefficient_nonneg (p : ℝ[X])
    (hp : ∀ t : ℝ, 0 ≤ p.eval t) (h0 : p.coeff 0 = 0) :
    0 ≤ p.coeff 2 := by
  have hmin : IsLocalMin (fun t : ℝ => p.eval t) 0 := by
    apply Filter.Eventually.of_forall
    intro t
    simpa [← Polynomial.coeff_zero_eq_eval_zero, h0] using hp t
  have h1 : p.coeff 1 = 0 := by
    have h := hmin.hasDerivAt_eq_zero (p.hasDerivAt 0)
    simpa [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_derivative] using h
  have hfac : p = X ^ 2 * p.divX.divX := by
    have ha := p.X_mul_divX_add
    have hb := p.divX.X_mul_divX_add
    simp only [coeff_divX, zero_add, h0, h1, C_0, add_zero] at ha hb
    calc
      p = X * p.divX := ha.symm
      _ = X * (X * p.divX.divX) := congrArg (fun q => X * q) hb.symm
      _ = X ^ 2 * p.divX.divX := by ring
  have hpos : ∀ t : ℝ, 0 < t → 0 ≤ p.divX.divX.eval t := by
    intro t ht
    have h := hp t
    rw [hfac, eval_mul, eval_pow, eval_X] at h
    exact nonneg_of_mul_nonneg_right h (sq_pos_of_pos ht)
  have hlim : Tendsto (fun t : ℝ => p.divX.divX.eval t)
      (𝓝[>] (0 : ℝ)) (𝓝 (p.divX.divX.eval 0)) :=
    p.divX.divX.continuous.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have h := ge_of_tendsto hlim (show ∀ᶠ t in 𝓝[>] (0 : ℝ), 0 ≤ p.divX.divX.eval t from
    Filter.eventually_of_mem self_mem_nhdsWithin (fun t ht => hpos t ht))
  simpa [← Polynomial.coeff_zero_eq_eval_zero, Polynomial.coeff_divX] using h

/-- Squared distance along a real affine motion, as a quadratic polynomial. -/
noncomputable def normSqMotionPolynomial (d h : ℂ) : ℝ[X] :=
  C (Complex.normSq d) + C (2 * (star d * h).re) * X + C (Complex.normSq h) * X ^ 2

private theorem eval_normSqMotionPolynomial (d h : ℂ) (t : ℝ) :
    (normSqMotionPolynomial d h).eval t = Complex.normSq (d + (t : ℂ) * h) := by
  simp [normSqMotionPolynomial, Complex.normSq_apply, Complex.mul_re, Complex.mul_im,
    Complex.add_re, Complex.add_im]
  ring

/-- The energy along the same motion. -/
noncomputable def energyMotionPolynomial (z h : Configuration) : ℝ[X] :=
  ∑ i, normSqMotionPolynomial (z i) (h i)

/-- The original discriminant along the same motion. -/
noncomputable def discriminantMotionPolynomial (z h : Configuration) : ℝ[X] :=
  ∏ p ∈ pairs, normSqMotionPolynomial (z p.1 - z p.2) (h p.1 - h p.2)

private theorem eval_energyMotionPolynomial (z h : Configuration) (t : ℝ) :
    (energyMotionPolynomial z h).eval t = normSum (motion z h t) := by
  simp [energyMotionPolynomial, eval_finsetSum, normSum, motion, eval_normSqMotionPolynomial]

private theorem energyMotionPolynomial_eq (z h : Configuration) :
    energyMotionPolynomial z h = C (normSum z) +
      C (2 * (innerMoment z h).re) * X + C (normSum h) * X ^ 2 := by
  unfold energyMotionPolynomial normSqMotionPolynomial
  simp only [Finset.sum_add_distrib, ← Finset.sum_mul, ← map_sum]
  congr 2
  simp [innerMoment, ← Finset.mul_sum]

private theorem eval_discriminantMotionPolynomial (z h : Configuration) (t : ℝ) :
    (discriminantMotionPolynomial z h).eval t = discriminant (motion z h t) := by
  simp only [discriminantMotionPolynomial, eval_prod, eval_normSqMotionPolynomial,
    discriminant, motion]
  apply Finset.prod_congr rfl
  intro p _
  congr 1
  ring

private theorem quadratic_power_coeff_one (a b : ℝ) (n : ℕ) :
    ((C a + C b * X ^ 2) ^ n).coeff 1 = 0 := by
  induction n with
  | zero => norm_num [Polynomial.coeff_one]
  | succ n ih =>
    rw [pow_succ, mul_coeff_one, ih]
    simp
private theorem quadratic_power_coeff_two (a b : ℝ) (n : ℕ) :
    ((C a + C b * X ^ 2) ^ (n+1)).coeff 2 = (n+1) * a ^ n * b := by
  induction n with
  | zero => norm_num [Polynomial.coeff_one]
  | succ n ih =>
    rw [pow_succ, coeff_mul, Finset.Nat.antidiagonal_eq_map]
    simp only [Finset.sum_map, Function.Embedding.coeFn_mk]
    simp [Finset.sum_range_succ, ih, quadratic_power_coeff_one,
      coeff_zero_eq_eval_zero]
    rw [pow_succ]
    ring

/-- Every actual global maximum satisfies the second-order coefficient inequality
for every affine direction. Both polynomials are formed from the original points. -/
theorem global_maximum_second_coefficient {z : Configuration} (hz : IsGlobalMaximum z)
    (h : Configuration) :
    (7 : ℝ) ^ 21 * (discriminantMotionPolynomial z h).coeff 2 ≤
      discriminant z * ((energyMotionPolynomial z h) ^ 21).coeff 2 := by
  let p : ℝ[X] := C (discriminant z) * (energyMotionPolynomial z h) ^ 21 -
    C ((7 : ℝ) ^ 21) * discriminantMotionPolynomial z h
  have hp : ∀ t : ℝ, 0 ≤ p.eval t := by
    intro t
    simp only [p, eval_sub, eval_mul, eval_C, eval_pow,
      eval_energyMotionPolynomial, eval_discriminantMotionPolynomial]
    exact sub_nonneg.mpr (global_maximum_polynomial_envelope hz (motion z h t))
  have h0 : p.coeff 0 = 0 := by
    rw [coeff_zero_eq_eval_zero]
    have hm : motion z h 0 = z := by
      funext i
      simp [motion]
    simp only [p, eval_sub, eval_mul, eval_C, eval_pow,
      eval_energyMotionPolynomial, eval_discriminantMotionPolynomial, hm, hz.1]
    ring
  have hsecond := second_coefficient_nonneg p hp h0
  simpa only [p, coeff_sub, coeff_C_mul, sub_nonneg] using hsecond

/-- Along an energy-tangent direction, the quadratic coefficient of the
original discriminant is bounded by the constrained second variation. -/
theorem global_maximum_tangent_second_coefficient {z : Configuration}
    (hz : IsGlobalMaximum z) (h : Configuration) (htangent : (innerMoment z h).re = 0) :
    (discriminantMotionPolynomial z h).coeff 2 ≤ 3 * discriminant z * normSum h := by
  have hsecond := global_maximum_second_coefficient hz h
  have henergy : energyMotionPolynomial z h =
      C (7 : ℝ) + C (normSum h) * X ^ 2 := by
    rw [energyMotionPolynomial_eq, hz.1, htangent]
    simp
  rw [henergy] at hsecond
  have hcoeff := quadratic_power_coeff_two 7 (normSum h) 20
  norm_num at hcoeff
  rw [hcoeff] at hsecond
  norm_num at hsecond
  nlinarith

#print axioms global_maximum_tangent_second_coefficient

private theorem mul_coeff_two (p q : ℝ[X]) :
    (p * q).coeff 2 = p.coeff 0 * q.coeff 2 + p.coeff 1 * q.coeff 1 +
      p.coeff 2 * q.coeff 0 := by
  rw [coeff_mul, Finset.Nat.antidiagonal_eq_map]
  simp [Finset.sum_range_succ]

private theorem motion_product_coefficients {ι : Type*} [DecidableEq ι]
    (s : Finset ι) (r : ι → ℂ) :
    (∏ i ∈ s, normSqMotionPolynomial 1 (r i)).coeff 0 = 1 ∧
    (∏ i ∈ s, normSqMotionPolynomial 1 (r i)).coeff 1 = 2 * (∑ i ∈ s, r i).re ∧
    (∏ i ∈ s, normSqMotionPolynomial 1 (r i)).coeff 2 =
      2 * (∑ i ∈ s, r i).re ^ 2 - (∑ i ∈ s, (r i) ^ 2).re := by
  induction s using Finset.induction_on with
  | empty => simp [Polynomial.coeff_one]
  | @insert a s ha ih =>
    simp only [Finset.prod_insert ha, Finset.sum_insert ha]
    rcases ih with ⟨h0, h1, h2⟩
    have hc0 : (normSqMotionPolynomial 1 (r a)).coeff 0 = 1 := by
      simp [normSqMotionPolynomial]
    have hc1 : (normSqMotionPolynomial 1 (r a)).coeff 1 = 2 * (r a).re := by
      simp [normSqMotionPolynomial, Polynomial.coeff_one]
    have hc2 : (normSqMotionPolynomial 1 (r a)).coeff 2 = Complex.normSq (r a) := by
      simp [normSqMotionPolynomial, Polynomial.coeff_one]
    constructor
    · rw [mul_coeff_zero, h0]
      simp [normSqMotionPolynomial]
    constructor
    · rw [mul_coeff_one, h0, h1, hc0, hc1]
      simp only [Complex.add_re]
      ring
    · rw [mul_coeff_two, h0, h1, h2, hc0, hc1, hc2]
      simp [Complex.normSq_apply, pow_two, Complex.mul_re]
      ring

private theorem normSqMotionPolynomial_factor (d h : ℂ) (hd : d ≠ 0) :
    normSqMotionPolynomial d h = C (Complex.normSq d) *
      normSqMotionPolynomial 1 (h / d) := by
  apply Polynomial.funext
  intro t
  rw [eval_normSqMotionPolynomial, eval_mul, eval_C, eval_normSqMotionPolynomial,
    ← Complex.normSq_mul]
  congr 1
  field_simp [hd]

private theorem discriminantMotionPolynomial_factor {z : Configuration}
    (hz : IsGlobalMaximum z) (h : Configuration) :
    discriminantMotionPolynomial z h = C (discriminant z) *
      ∏ p ∈ pairs, normSqMotionPolynomial 1 ((h p.1 - h p.2) / (z p.1 - z p.2)) := by
  unfold discriminantMotionPolynomial
  calc
    (∏ p ∈ pairs, normSqMotionPolynomial (z p.1 - z p.2) (h p.1 - h p.2)) =
        ∏ p ∈ pairs, C (Complex.normSq (z p.1 - z p.2)) *
          normSqMotionPolynomial 1 ((h p.1 - h p.2) / (z p.1 - z p.2)) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact normSqMotionPolynomial_factor _ _
        (global_maximum_sub_ne_zero hz (ne_of_lt (Finset.mem_filter.mp hp).2))
    _ = _ := by
      rw [Finset.prod_mul_distrib, ← map_prod]
      rfl

/-- The complex quadratic form governing the second variation of log discriminant. -/
noncomputable def pairSquareSum (z h : Configuration) : ℂ :=
  ∑ p ∈ pairs, ((h p.1 - h p.2) / (z p.1 - z p.2)) ^ 2

private theorem discriminantMotionPolynomial_coeff_two {z : Configuration}
    (hz : IsGlobalMaximum z) (h : Configuration) :
    (discriminantMotionPolynomial z h).coeff 2 = discriminant z *
      (2 * (pairSum z h).re ^ 2 - (pairSquareSum z h).re) := by
  rw [discriminantMotionPolynomial_factor hz h, coeff_C_mul,
    (motion_product_coefficients pairs
      (fun p => (h p.1 - h p.2) / (z p.1 - z p.2))).2.2]
  rfl

/-- A tangent direction cannot have a positive constrained second variation. -/
theorem global_maximum_second_variation {z : Configuration} (hz : IsGlobalMaximum z)
    (h : Configuration) (htangent : (innerMoment z h).re = 0) :
    -3 * normSum h ≤ (pairSquareSum z h).re := by
  have hpairs : (pairSum z h).re = 0 := by
    have hfirst := global_maximum_pairSum_real hz h
    rw [htangent] at hfirst
    linarith
  have hsecond := global_maximum_tangent_second_coefficient hz h htangent
  rw [discriminantMotionPolynomial_coeff_two hz h, hpairs] at hsecond
  have hmul : discriminant z * (-(pairSquareSum z h).re) ≤
      discriminant z * (3 * normSum h) := by
    nlinarith only [hsecond]
  have h := (mul_le_mul_iff_right₀ (global_maximum_positive hz)).mp hmul
  linarith

#print axioms global_maximum_second_variation


end N7.Analysis
