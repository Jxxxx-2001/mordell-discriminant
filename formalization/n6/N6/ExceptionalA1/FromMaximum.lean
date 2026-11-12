import N6.ExceptionalA1.Contradiction
import N6.ResultantMinors.Necessity

set_option autoImplicit false

namespace N6.ExceptionalA1
open N6.SparseCheck N6.ResultantMinors Polynomial

theorem scaled_maximum_b_zero_d_zero {z : N6.Configuration}
    (hz : N6.IsGlobalMaximum z) {α : ℂ} (hα : α ≠ 0) (c d e : ℂ)
    (hp : N6.rootPolynomial (N6.scaleConfiguration α z) =
      N6.coefficientSextic 1 0 c d e) : d = 0 := by
  by_contra hd
  have hD := scaled_maximum_originalD_ne hz hα 0 c d e hp
  obtain ⟨h0,h1,h2,h3⟩ := scaled_maximum_original_equations hz hα 0 c d e hp
  have hr := N6.physical_resultant_zero_coefficient _ _ _
    (N6.scaled_dual_physical hz hα) 3 (by
      rw [hp]
      simp [N6.coefficientSextic, coeff_C_mul, coeff_X_pow])
  rw [stationaryR0_eq_liftY (N6.scaled_dualStationaryPair hz hα) 0 c d e hp,
    coeff_liftY] at hr
  let t : ℂ := (d*N6.Chart.originalD 0 c d e)⁻¹
  have hs : t*d*N6.Chart.originalD 0 c d e-1 = 0 := by
    dsimp [t]
    rw [mul_assoc, inv_mul_cancel₀ (mul_ne_zero hd hD), sub_self]
  exact impossible c d e t h0 h1 h2 h3 hr hs

#print axioms scaled_maximum_b_zero_d_zero
end N6.ExceptionalA1
