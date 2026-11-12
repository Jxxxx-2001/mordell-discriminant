import N6.Analysis.RootPolynomial
import Mathlib.RingTheory.Polynomial.ScaleRoots
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

set_option autoImplicit false

namespace N6

noncomputable def scaleConfiguration (α : ℂ) (z : Configuration) : Configuration :=
  fun i => α * z i

noncomputable def forceParameter (w : Configuration) : ℝ := 30 / normSum w

noncomputable def dualConfiguration (w : Configuration) : Configuration :=
  fun i => 2 * force w i

theorem force_eq_half_dual (w : Configuration) (i : Fin 6) :
    force w i = dualConfiguration w i / 2 := by
  unfold dualConfiguration
  ring

theorem force_scale (z : Configuration) {α : ℂ} (hα : α ≠ 0) (i : Fin 6) :
    force (scaleConfiguration α z) i = force z i / α := by
  unfold force scaleConfiguration
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i
  · simp [hj]
  · simp only [if_neg hj]
    rw [← mul_sub]
    field_simp

theorem force_star (z : Configuration) (i : Fin 6) :
    force (fun j => star (z j)) i = star (force z i) := by
  unfold force
  rw [star_sum]
  apply Finset.sum_congr rfl
  intro j _
  by_cases hj : j = i <;> simp [hj]

theorem scaled_injective {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) : Function.Injective (scaleConfiguration α z) := by
  intro i j hij
  exact global_maximum_injective hz ((mul_left_cancel₀ hα) hij)

theorem scaled_sub_ne_zero {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) {i j : Fin 6} (hij : i ≠ j) :
    scaleConfiguration α z i - scaleConfiguration α z j ≠ 0 := by
  exact sub_ne_zero.mpr ((scaled_injective hz hα).ne hij)

theorem scaled_centered {z : Configuration} (hz : IsGlobalMaximum z) (α : ℂ) :
    ∑ i, scaleConfiguration α z i = 0 := by
  simp only [scaleConfiguration, ← Finset.mul_sum, global_maximum_centered hz, mul_zero]

theorem scaled_normSum {z : Configuration} (hz : IsGlobalMaximum z) (α : ℂ) :
    normSum (scaleConfiguration α z) = 6 * Complex.normSq α := by
  change normSum (fun i => α * z i) = _
  rw [normSum_scale, hz.1]
  ring

theorem scaled_normSum_pos {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) : 0 < normSum (scaleConfiguration α z) := by
  rw [scaled_normSum hz]
  exact mul_pos (by norm_num) (Complex.normSq_pos.mpr hα)

theorem scaled_normSum_ne_zero {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) : normSum (scaleConfiguration α z) ≠ 0 :=
  ne_of_gt (scaled_normSum_pos hz hα)

theorem forceParameter_pos {w : Configuration} (hq : 0 < normSum w) :
    0 < forceParameter w := by
  exact div_pos (by norm_num) hq

theorem forceParameter_ne_zero {w : Configuration} (hq : 0 < normSum w) :
    forceParameter w ≠ 0 := ne_of_gt (forceParameter_pos hq)

theorem forceParameter_cast_ne_zero {w : Configuration} (hq : 0 < normSum w) :
    (forceParameter w : ℂ) ≠ 0 :=
  Complex.ofReal_ne_zero.mpr (forceParameter_ne_zero hq)

theorem scaled_forceParameter_pos {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) : 0 < forceParameter (scaleConfiguration α z) :=
  forceParameter_pos (scaled_normSum_pos hz hα)

theorem scaled_forceParameter_ne_zero {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) : forceParameter (scaleConfiguration α z) ≠ 0 :=
  ne_of_gt (scaled_forceParameter_pos hz hα)

theorem scaled_forceParameter_cast_ne_zero {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) :
    (forceParameter (scaleConfiguration α z) : ℂ) ≠ 0 :=
  forceParameter_cast_ne_zero (scaled_normSum_pos hz hα)

theorem scaled_forceParameter {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) :
    forceParameter (scaleConfiguration α z) = 5 / Complex.normSq α := by
  have hn : Complex.normSq α ≠ 0 := mt Complex.normSq_eq_zero.mp hα
  unfold forceParameter
  rw [scaled_normSum hz]
  field_simp [hn] <;> ring

theorem scaled_dual_explicit {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) (i : Fin 6) :
    dualConfiguration (scaleConfiguration α z) i = 5 * star (z i) / α := by
  unfold dualConfiguration
  rw [force_scale z hα, global_maximum_force hz]
  ring

theorem scaled_dual_physical {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) (i : Fin 6) :
    dualConfiguration (scaleConfiguration α z) i =
      (forceParameter (scaleConfiguration α z) : ℂ) * star (scaleConfiguration α z i) := by
  have hs : star α ≠ 0 := star_ne_zero.mpr hα
  have hc : (starRingEnd ℂ) α ≠ 0 := by simpa only [Complex.star_def] using hs
  rw [scaled_dual_explicit hz hα i, scaled_forceParameter hz hα]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat, scaleConfiguration, star_mul,
    Complex.star_def]
  rw [Complex.normSq_eq_conj_mul_self]
  field_simp [hα, hc] <;> ring

theorem scaled_force_physical {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) (i : Fin 6) :
    force (scaleConfiguration α z) i =
      ((forceParameter (scaleConfiguration α z) : ℂ) / 2) *
        star (scaleConfiguration α z i) := by
  have h := scaled_dual_physical hz hα i
  unfold dualConfiguration at h
  linear_combination (1 / 2 : ℂ) * h

theorem scaled_force_sum {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) (i : Fin 6) :
    (∑ j ∈ Finset.univ.erase i,
      1 / (scaleConfiguration α z i - scaleConfiguration α z j)) =
      ((forceParameter (scaleConfiguration α z) : ℂ) / 2) *
        (starRingEnd ℂ) (scaleConfiguration α z i) := by
  rw [← force_eq_sum_erase]
  simpa only [Complex.star_def] using scaled_force_physical hz hα i

theorem normalization_derivative_eval_ne {w : Configuration} (hw : Function.Injective w)
    (i : Fin 6) : (rootPolynomial w).derivative.eval (w i) ≠ 0 := by
  rw [rootPolynomial_derivative_eval]
  exact rootCofactor_eval_ne hw i

theorem dual_eq_derivative_ratio {w : Configuration} (hw : Function.Injective w)
    (i : Fin 6) :
    dualConfiguration w i =
      (rootPolynomial w).derivative.derivative.eval (w i) /
        (rootPolynomial w).derivative.eval (w i) := by
  have hp := normalization_derivative_eval_ne hw i
  unfold dualConfiguration
  rw [rootPolynomial_second_derivative_eval hw]
  field_simp [hp] <;> ring

theorem rootPolynomial_dual_equation {w : Configuration} (hw : Function.Injective w)
    (i : Fin 6) :
    (rootPolynomial w).derivative.derivative.eval (w i) =
      dualConfiguration w i * (rootPolynomial w).derivative.eval (w i) := by
  rw [rootPolynomial_second_derivative_eval hw]
  unfold dualConfiguration
  ring

theorem scaled_dual_derivative_ratio {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) (i : Fin 6) :
    dualConfiguration (scaleConfiguration α z) i =
      (rootPolynomial (scaleConfiguration α z)).derivative.derivative.eval
          (scaleConfiguration α z i) /
        (rootPolynomial (scaleConfiguration α z)).derivative.eval
          (scaleConfiguration α z i) :=
  dual_eq_derivative_ratio (scaled_injective hz hα) i

theorem scaled_dual_injective {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) :
    Function.Injective (dualConfiguration (scaleConfiguration α z)) := by
  intro i j hij
  apply global_maximum_injective hz
  apply star_injective
  rw [scaled_dual_explicit hz hα i, scaled_dual_explicit hz hα j] at hij
  exact (mul_left_cancel₀ (by norm_num : (5 : ℂ) ≠ 0)) ((div_left_inj' hα).mp hij)

theorem scaled_dual_sub_ne_zero {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) {i j : Fin 6} (hij : i ≠ j) :
    dualConfiguration (scaleConfiguration α z) i -
      dualConfiguration (scaleConfiguration α z) j ≠ 0 := by
  exact sub_ne_zero.mpr ((scaled_dual_injective hz hα).ne hij)

theorem scaled_dual_centered {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) :
    ∑ i, dualConfiguration (scaleConfiguration α z) i = 0 := by
  simp only [scaled_dual_explicit hz hα, ← Finset.sum_div, ← Finset.mul_sum,
    ← star_sum, global_maximum_centered hz, star_zero, mul_zero, zero_div]

theorem scaled_dual_force {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) (i : Fin 6) :
    force (dualConfiguration (scaleConfiguration α z)) i = scaleConfiguration α z i / 2 := by
  have ht : (5 : ℂ) / α ≠ 0 := div_ne_zero (by norm_num) hα
  have he : dualConfiguration (scaleConfiguration α z) =
      scaleConfiguration ((5 : ℂ) / α) (fun j => star (z j)) := by
    funext j
    rw [scaled_dual_explicit hz hα j]
    dsimp [scaleConfiguration]
    ring
  rw [he, force_scale _ ht, force_star, global_maximum_force hz]
  simp only [star_mul, star_div₀, star_ofNat, star_star, scaleConfiguration]
  field_simp [hα] <;> ring

theorem scaled_dual_force_sum {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) (i : Fin 6) :
    (∑ j ∈ Finset.univ.erase i,
      1 / (dualConfiguration (scaleConfiguration α z) i -
        dualConfiguration (scaleConfiguration α z) j)) = scaleConfiguration α z i / 2 := by
  rw [← force_eq_sum_erase]
  exact scaled_dual_force hz hα i

theorem scaled_dual_moment {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) :
    ∑ i, scaleConfiguration α z i * dualConfiguration (scaleConfiguration α z) i = 30 := by
  calc
    ∑ i, scaleConfiguration α z i * dualConfiguration (scaleConfiguration α z) i =
        5 * (normSum z : ℂ) := by
      simp only [normSum, Complex.ofReal_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [scaled_dual_explicit hz hα i, Complex.normSq_eq_conj_mul_self]
      simp only [scaleConfiguration, Complex.star_def]
      field_simp [hα] <;> ring
    _ = 30 := by rw [hz.1]; norm_num


open Polynomial

theorem rootPolynomial_monic (z : Configuration) : (rootPolynomial z).Monic := by
  exact monic_prod_of_monic _ _ (fun _ _ => monic_X_sub_C _)

theorem rootPolynomial_natDegree (z : Configuration) : (rootPolynomial z).natDegree = 6 := by
  unfold rootPolynomial
  rw [natDegree_prod_of_monic (Finset.univ : Finset (Fin 6))
    (fun i => X - C (z i)) (fun i _ => monic_X_sub_C (z i))]
  simp

theorem rootPolynomial_coeff_five (z : Configuration) :
    (rootPolynomial z).coeff 5 = -∑ i, z i := by
  simpa only [rootPolynomial, Finset.card_univ, Fintype.card_fin] using
    prod_X_sub_C_coeff_card_pred Finset.univ z (by decide)

theorem scaled_rootPolynomial_coeff_five_zero {z : Configuration}
    (hz : IsGlobalMaximum z) (α : ℂ) :
    (rootPolynomial (scaleConfiguration α z)).coeff 5 = 0 := by
  rw [rootPolynomial_coeff_five, scaled_centered hz, neg_zero]

theorem rootPolynomial_scale (z : Configuration) (α : ℂ) :
    rootPolynomial (scaleConfiguration α z) = (rootPolynomial z).scaleRoots α := by
  unfold rootPolynomial scaleConfiguration
  induction (Finset.univ : Finset (Fin 6)) using Finset.induction_on with
  | empty => simp
  | @insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha,
      mul_scaleRoots_of_noZeroDivisors, X_sub_C_scaleRoots, ih]
    simp only [mul_comm (z a) α]

theorem rootPolynomial_scale_coeff (z : Configuration) (α : ℂ) (j : ℕ) :
    (rootPolynomial (scaleConfiguration α z)).coeff j =
      (rootPolynomial z).coeff j * α^(6-j) := by
  rw [rootPolynomial_scale, coeff_scaleRoots, rootPolynomial_natDegree]

noncomputable def rootCoefficientA (z : Configuration) : ℂ :=
  (rootPolynomial z).coeff 4

theorem rootCoefficientA_scale (z : Configuration) (α : ℂ) :
    rootCoefficientA (scaleConfiguration α z) = rootCoefficientA z * α^2 := by
  unfold rootCoefficientA
  rw [rootPolynomial_scale_coeff]

/-- Explicit complex powers provide the same nonzero normalization interface as the
five-point proof, without importing the fundamental theorem of algebra. -/
theorem normalize_nonzero (a : ℂ) (ha : a ≠ 0) (n : ℕ) (hn : 0 < n) :
    ∃ α : ℂ, α ≠ 0 ∧ a * α^n = 1 := by
  let α : ℂ := a⁻¹ ^ ((n : ℂ)⁻¹)
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hpow : α^n = a⁻¹ := Complex.cpow_nat_inv_pow _ hn0
  have hα : α ≠ 0 := by
    intro hzero
    rw [hzero, zero_pow hn0] at hpow
    exact (inv_ne_zero ha) hpow.symm
  exact ⟨α, hα, by rw [hpow, mul_inv_cancel₀ ha]⟩

theorem exists_normalize_coefficientA (z : Configuration) (hA : rootCoefficientA z ≠ 0) :
    ∃ α : ℂ, α ≠ 0 ∧ rootCoefficientA (scaleConfiguration α z) = 1 := by
  obtain ⟨α, hα, hnorm⟩ := normalize_nonzero (rootCoefficientA z) hA 2 (by decide)
  exact ⟨α, hα, by rw [rootCoefficientA_scale]; exact hnorm⟩

theorem global_maximum_normalize_A {z : Configuration} (hz : IsGlobalMaximum z)
    (hA : rootCoefficientA z ≠ 0) :
    ∃ α : ℂ, α ≠ 0 ∧ rootCoefficientA (scaleConfiguration α z) = 1 ∧
      0 < normSum (scaleConfiguration α z) := by
  obtain ⟨α, hα, hA1⟩ := exists_normalize_coefficientA z hA
  exact ⟨α, hα, hA1, scaled_normSum_pos hz hα⟩

end N6
