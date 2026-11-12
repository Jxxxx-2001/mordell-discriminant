import N6.Analysis.DualStationarity
import N6.Analysis.PhysicalScalar

set_option autoImplicit false

namespace N6
open Polynomial

theorem rootPolynomial_map_star (w : Configuration) :
    (rootPolynomial w).map (starRingEnd ℂ) = rootPolynomial (fun i => star (w i)) := by
  unfold rootPolynomial
  simp only [Polynomial.map_prod, Polynomial.map_sub, Polynomial.map_X,
    Polynomial.map_C, Complex.star_def]

theorem physical_root_coefficient (w y : Configuration) (κ : ℝ)
    (hy : ∀ i, y i = (κ : ℂ)*star (w i)) (j : ℕ) :
    (rootPolynomial y).coeff j =
      (starRingEnd ℂ) ((rootPolynomial w).coeff j) * (κ : ℂ)^(6-j) := by
  have he : y = scaleConfiguration (κ : ℂ) (fun i => star (w i)) := funext hy
  rw [he, rootPolynomial_scale_coeff, ← rootPolynomial_map_star, coeff_map]

theorem physical_resultant_coefficient (w y : Configuration) (κ : ℝ)
    (hy : ∀ i, y i = (κ : ℂ)*star (w i)) (j : ℕ) :
    (stationaryR0 w y).coeff j = complexDiscriminant w *
      ((starRingEnd ℂ) ((rootPolynomial w).coeff j) * (κ : ℂ)^(6-j)) := by
  rw [stationaryR0, coeff_C_mul, physical_root_coefficient w y κ hy j]

theorem physical_resultant_zero_coefficient (w y : Configuration) (κ : ℝ)
    (hy : ∀ i, y i = (κ : ℂ)*star (w i)) (j : ℕ)
    (hj : (rootPolynomial w).coeff j = 0) : (stationaryR0 w y).coeff j = 0 := by
  rw [physical_resultant_coefficient w y κ hy j, hj, map_zero, zero_mul, mul_zero]

theorem scaled_maximum_resultant_four {z : Configuration} (hz : IsGlobalMaximum z)
    {α : ℂ} (hα : α ≠ 0) (hA : rootCoefficientA (scaleConfiguration α z) = 1) :
    (stationaryR0 (scaleConfiguration α z)
      (dualConfiguration (scaleConfiguration α z))).coeff 4 =
      complexDiscriminant (scaleConfiguration α z) *
        (physicalScalar (scaleConfiguration α z) : ℂ) := by
  rw [physical_resultant_coefficient _ _ _ (scaled_dual_physical hz hα) 4]
  change _ * ((starRingEnd ℂ) (rootCoefficientA (scaleConfiguration α z)) *
    (forceParameter (scaleConfiguration α z) : ℂ)^2) = _
  rw [hA, map_one, one_mul]
  simp only [physicalScalar, Complex.ofReal_pow]

#print axioms physical_root_coefficient
#print axioms physical_resultant_zero_coefficient
#print axioms scaled_maximum_resultant_four
end N6
