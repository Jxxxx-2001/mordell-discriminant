import N6.Analysis.Normalization

set_option autoImplicit false

namespace N6
open Polynomial

noncomputable def coefficientSextic (A b c d e : ℂ) : ℂ[X] :=
  X^6 + C A*X^4 + C b*X^3 + C c*X^2 + C d*X + C e

theorem rootPolynomial_as_sextic (w : Configuration) (hc : ∑ i, w i = 0) :
    rootPolynomial w = coefficientSextic (rootCoefficientA w)
      ((rootPolynomial w).coeff 3) ((rootPolynomial w).coeff 2)
      ((rootPolynomial w).coeff 1) ((rootPolynomial w).coeff 0) := by
  have h6 : (rootPolynomial w).coeff 6 = 1 := by
    rw [← rootPolynomial_natDegree w]
    exact (rootPolynomial_monic w).coeff_natDegree
  have h5 : (rootPolynomial w).coeff 5 = 0 := by
    rw [rootPolynomial_coeff_five, hc, neg_zero]
  have hd : (rootPolynomial w).natDegree < 7 := by rw [rootPolynomial_natDegree]; decide
  calc
    rootPolynomial w = ∑ j ∈ Finset.range 7, C ((rootPolynomial w).coeff j)*X^j :=
      (rootPolynomial w).as_sum_range_C_mul_X_pow' hd
    _ = _ := by
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
        h6, h5, map_one, map_zero, one_mul, zero_mul, pow_zero, pow_one,
        mul_one, add_zero, coefficientSextic, rootCoefficientA]
      ring

theorem normalized_rootPolynomial_as_sextic (w : Configuration)
    (hc : ∑ i, w i = 0) (hA : rootCoefficientA w = 1) :
    rootPolynomial w = coefficientSextic 1
      ((rootPolynomial w).coeff 3) ((rootPolynomial w).coeff 2)
      ((rootPolynomial w).coeff 1) ((rootPolynomial w).coeff 0) := by
  simpa only [hA] using rootPolynomial_as_sextic w hc

#print axioms rootPolynomial_as_sextic
#print axioms normalized_rootPolynomial_as_sextic
end N6
