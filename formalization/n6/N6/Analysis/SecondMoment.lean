import N6.Analysis.PhysicalScalar

set_option autoImplicit false

namespace N6
open Polynomial

/-- The second elementary coefficient of the six-root polynomial is the sum of
its fifteen pairwise root products. This is only a small coefficient calculation. -/
theorem rootCoefficientA_eq_pair_products (w : Configuration) :
    rootCoefficientA w =
      w 0*w 1 + w 0*w 2 + w 0*w 3 + w 0*w 4 + w 0*w 5 +
      w 1*w 2 + w 1*w 3 + w 1*w 4 + w 1*w 5 +
      w 2*w 3 + w 2*w 4 + w 2*w 5 +
      w 3*w 4 + w 3*w 5 + w 4*w 5 := by
  simp [rootCoefficientA, rootPolynomial, Fin.prod_univ_succ, sub_mul,
    coeff_sub, coeff_X_mul, coeff_C_mul, coeff_X] <;> ring

/-- The degree-two Newton/Vieta identity, without assumptions on the roots. -/
theorem rootCoefficientA_secondMoment (w : Configuration) :
    (2 : ℂ) * rootCoefficientA w = (∑ i, w i)^2 - ∑ i, (w i)^2 := by
  rw [rootCoefficientA_eq_pair_products, sum_expand w, sum_expand (fun i => (w i)^2)]
  ring

theorem secondMoment_eq_neg_two_of_centered_normalized {w : Configuration}
    (hcenter : ∑ i, w i = 0) (hA : rootCoefficientA w = 1) :
    ∑ i, (w i)^2 = (-2 : ℂ) := by
  have h := rootCoefficientA_secondMoment w
  rw [hcenter, hA] at h
  linear_combination h

theorem physicalScalar_bounds_of_centered_normalized {w : Configuration}
    (hcenter : ∑ i, w i = 0) (hA : rootCoefficientA w = 1) :
    0 < physicalScalar w ∧ physicalScalar w ≤ 225 :=
  physicalScalar_bounds_of_moment (secondMoment_eq_neg_two_of_centered_normalized hcenter hA)

theorem physicalScalar_endpoint_all_re_zero_of_centered_normalized {w : Configuration}
    (hcenter : ∑ i, w i = 0) (hA : rootCoefficientA w = 1)
    (ha : physicalScalar w = 225) : ∀ i, (w i).re = 0 :=
  physicalScalar_endpoint_all_re_zero
    (secondMoment_eq_neg_two_of_centered_normalized hcenter hA) ha

theorem scaled_maximum_normalized_secondMoment {z : Configuration}
    (hz : IsGlobalMaximum z) (α : ℂ)
    (hA : rootCoefficientA (scaleConfiguration α z) = 1) :
    ∑ i, (scaleConfiguration α z i)^2 = (-2 : ℂ) :=
  secondMoment_eq_neg_two_of_centered_normalized (scaled_centered hz α) hA

theorem scaled_maximum_normalized_physicalScalar_bounds {z : Configuration}
    (hz : IsGlobalMaximum z) (α : ℂ)
    (hA : rootCoefficientA (scaleConfiguration α z) = 1) :
    0 < physicalScalar (scaleConfiguration α z) ∧
      physicalScalar (scaleConfiguration α z) ≤ 225 :=
  physicalScalar_bounds_of_centered_normalized (scaled_centered hz α) hA

theorem scaled_maximum_normalized_endpoint_all_re_zero {z : Configuration}
    (hz : IsGlobalMaximum z) (α : ℂ)
    (hA : rootCoefficientA (scaleConfiguration α z) = 1)
    (ha : physicalScalar (scaleConfiguration α z) = 225) :
    ∀ i, (scaleConfiguration α z i).re = 0 :=
  physicalScalar_endpoint_all_re_zero_of_centered_normalized (scaled_centered hz α) hA ha

theorem scaled_maximum_normalized_endpoint_coeff_three_square {z : Configuration}
    (hz : IsGlobalMaximum z) (α : ℂ)
    (hA : rootCoefficientA (scaleConfiguration α z) = 1)
    (ha : physicalScalar (scaleConfiguration α z) = 225) :
    (((rootPolynomial (scaleConfiguration α z)).coeff 3)^2).im = 0 ∧
      (((rootPolynomial (scaleConfiguration α z)).coeff 3)^2).re ≤ 0 :=
  rootPolynomial_coeff_three_square_physical
    (scaled_maximum_normalized_endpoint_all_re_zero hz α hA ha)

end N6
