import N6.Analysis.SecondMoment
import N6.Analysis.SexticCoefficients

set_option autoImplicit false

namespace N6
open Polynomial

theorem sextic_coeff_three (A b c d e : ℂ) :
    (coefficientSextic A b c d e).coeff 3 = b := by
  simp [coefficientSextic, coeff_C_mul, coeff_X_pow]

theorem normalized_endpoint_excludes_positive_B {z : Configuration}
    (hz : IsGlobalMaximum z) (α : ℂ)
    (hA : rootCoefficientA (scaleConfiguration α z) = 1)
    (ha : physicalScalar (scaleConfiguration α z) = 225)
    (b c d e : ℂ)
    (hp : rootPolynomial (scaleConfiguration α z) = coefficientSextic 1 b c d e)
    (hB : 0 < (b^2).re) : False := by
  have h := (scaled_maximum_normalized_endpoint_coeff_three_square hz α hA ha).2
  rw [hp, sextic_coeff_three] at h
  exact (not_lt_of_ge h) hB

#print axioms normalized_endpoint_excludes_positive_B
end N6
