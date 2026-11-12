import N7.Analysis.RootPolynomial

set_option autoImplicit false

namespace N7.Analysis

noncomputable def scaleConfiguration (α : ℂ) (z : Configuration) : Configuration :=
  fun i => α * z i

noncomputable def dualConfiguration (w : Configuration) : Configuration :=
  fun i => 2 * force w i

theorem force_scale (z : Configuration) {α : ℂ} (hα : α ≠ 0) (i : Fin 7) :
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

theorem scaled_injective {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) : Function.Injective (scaleConfiguration α z) := by
  intro i j hij
  exact global_maximum_injective hz ((mul_left_cancel₀ hα) hij)

theorem scaled_centered {z : Configuration} (hz : IsGlobalMaximum z) (α : ℂ) :
    ∑ i, scaleConfiguration α z i = 0 := by
  simp only [scaleConfiguration, ← Finset.mul_sum, global_maximum_centered hz, mul_zero]

theorem scaled_normSum {z : Configuration} (hz : IsGlobalMaximum z) (α : ℂ) :
    normSum (scaleConfiguration α z) = 7 * Complex.normSq α := by
  change normSum (fun i => α * z i) = _
  rw [normSum_scale, hz.1]
  ring

theorem scaled_normSum_pos {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) : 0 < normSum (scaleConfiguration α z) := by
  rw [scaled_normSum hz]
  exact mul_pos (by norm_num) (Complex.normSq_pos.mpr hα)

theorem scaled_forceParameter {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) :
    forceParameter (scaleConfiguration α z) = 6 / Complex.normSq α := by
  have hn : Complex.normSq α ≠ 0 := mt Complex.normSq_eq_zero.mp hα
  unfold forceParameter
  rw [scaled_normSum hz]
  field_simp [hn] <;> ring

theorem scaled_dual_explicit {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) (i : Fin 7) :
    dualConfiguration (scaleConfiguration α z) i = 6 * star (z i) / α := by
  unfold dualConfiguration
  rw [force_scale z hα, global_maximum_force hz]
  ring

theorem scaled_dual_physical {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) (i : Fin 7) :
    dualConfiguration (scaleConfiguration α z) i =
      (forceParameter (scaleConfiguration α z) : ℂ) *
        (starRingEnd ℂ) (scaleConfiguration α z i) := by
  have hc : (starRingEnd ℂ) α ≠ 0 := (map_ne_zero (starRingEnd ℂ)).mpr hα
  rw [scaled_dual_explicit hz hα i, scaled_forceParameter hz hα]
  simp only [Complex.ofReal_div, Complex.ofReal_ofNat, scaleConfiguration,
    map_mul, Complex.star_def]
  rw [Complex.normSq_eq_conj_mul_self]
  field_simp [hα, hc] <;> ring

theorem scaled_dual_physical_fun {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) :
    dualConfiguration (scaleConfiguration α z) =
      fun i => (forceParameter (scaleConfiguration α z) : ℂ) *
        (starRingEnd ℂ) (scaleConfiguration α z i) :=
  funext (scaled_dual_physical hz hα)

end N7.Analysis
