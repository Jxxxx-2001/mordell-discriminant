import N6.Analysis.SexticCoefficients

set_option autoImplicit false

namespace N6
open Polynomial

theorem coefficient_zero_of_scaled {z : Configuration} {α : ℂ} (hα : α ≠ 0)
    (j : ℕ) (h : (rootPolynomial (scaleConfiguration α z)).coeff j = 0) :
    (rootPolynomial z).coeff j = 0 := by
  rw [rootPolynomial_scale_coeff] at h
  exact (mul_eq_zero.mp h).resolve_right (pow_ne_zero _ hα)

theorem scaled_coefficient_zero {z : Configuration} (α : ℂ) (j : ℕ)
    (h : (rootPolynomial z).coeff j = 0) :
    (rootPolynomial (scaleConfiguration α z)).coeff j = 0 := by
  rw [rootPolynomial_scale_coeff, h, zero_mul]

theorem normalize_root_coefficient (z : Configuration) (j : ℕ) (hj : j < 6)
    (hc : (rootPolynomial z).coeff j ≠ 0) :
    ∃ α : ℂ, α ≠ 0 ∧ (rootPolynomial (scaleConfiguration α z)).coeff j = 1 := by
  obtain ⟨α,hα,he⟩ := normalize_nonzero ((rootPolynomial z).coeff j) hc (6-j) (by omega)
  exact ⟨α,hα, by rw [rootPolynomial_scale_coeff]; exact he⟩

theorem trinomial_of_vanishing_coefficients (z : Configuration)
    (hcenter : ∑ i, z i = 0) (hA : rootCoefficientA z = 0)
    (hc : (rootPolynomial z).coeff 2 = 0) (hd : (rootPolynomial z).coeff 1 = 0) :
    rootPolynomial z = X^6 + C ((rootPolynomial z).coeff 3)*X^3 +
      C ((rootPolynomial z).coeff 0) := by
  simpa only [hA, hc, hd, coefficientSextic, map_zero, zero_mul, add_zero] using
    rootPolynomial_as_sextic z hcenter

#print axioms coefficient_zero_of_scaled
#print axioms normalize_root_coefficient
#print axioms trinomial_of_vanishing_coefficients
end N6
