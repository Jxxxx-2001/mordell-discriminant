import N6.Analysis.ShapeTransport
import N6.Analysis.GenericValue
import N6.Exceptional.All
import N6.Symmetry.TripleBound

set_option autoImplicit false

namespace N6
open Polynomial

/-- Exhaust the zero-A coefficient charts using nonzero coefficient scaling.
Every scaling is about the prescribed origin. -/
theorem global_maximum_A_zero_classification {z : Configuration}
    (hz : IsGlobalMaximum z) (hA : rootCoefficientA z = 0) : IsCenteredPentagon z := by
  have exclude_trinomial (hp : rootPolynomial z = X^6 + C ((rootPolynomial z).coeff 3)*X^3 +
      C ((rootPolynomial z).coeff 0)) : False := by
    have hb := Symmetry.Triple.trinomial_bound z hz.1 (global_maximum_injective hz) _ _ hp
    exact (not_lt_of_ge (Pentagon.global_maximum_lower_bound hz))
      (hb.trans_lt GenericValue.six_pow_six_lt_sharp)
  by_cases hb : (rootPolynomial z).coeff 3 = 0
  · by_cases hc : (rootPolynomial z).coeff 2 = 0
    · by_cases hd : (rootPolynomial z).coeff 1 = 0
      · exact False.elim (exclude_trinomial
          (trinomial_of_vanishing_coefficients z (global_maximum_centered hz) hA hc hd))
      · obtain ⟨α,hα,hn⟩ := normalize_root_coefficient z 1 (by decide) hd
        have hA' : rootCoefficientA (scaleConfiguration α z) = 0 := by
          rw [rootCoefficientA_scale, hA, zero_mul]
        have hb' := scaled_coefficient_zero α 3 hb
        have hc' := scaled_coefficient_zero α 2 hc
        let e := (rootPolynomial (scaleConfiguration α z)).coeff 0
        have hp : rootPolynomial (scaleConfiguration α z) = coefficientSextic 0 0 0 1 e := by
          simpa only [hA', hb', hc', hn] using
            rootPolynomial_as_sextic (scaleConfiguration α z) (scaled_centered hz α)
        have he := Exceptional.ChartIV_of_scaled_maximum hz hα e hp
        have hbin : rootPolynomial (scaleConfiguration α z) = X^6 + C (1 : ℂ)*X := by
          simpa only [he, coefficientSextic, map_zero, map_one, zero_mul,
            one_mul, zero_add, add_zero] using hp
        exact Pentagon.centered_of_scaled_binomial z hz.1 α 1 hα (by norm_num) hbin
    · obtain ⟨α,hα,hn⟩ := normalize_root_coefficient z 2 (by decide) hc
      have hA' : rootCoefficientA (scaleConfiguration α z) = 0 := by
        rw [rootCoefficientA_scale, hA, zero_mul]
      have hb' := scaled_coefficient_zero α 3 hb
      let d := (rootPolynomial (scaleConfiguration α z)).coeff 1
      let e := (rootPolynomial (scaleConfiguration α z)).coeff 0
      have hp : rootPolynomial (scaleConfiguration α z) = coefficientSextic 0 0 1 d e := by
        simpa only [hA', hb', hn] using
          rootPolynomial_as_sextic (scaleConfiguration α z) (scaled_centered hz α)
      exact False.elim (Exceptional.ChartIII_of_scaled_maximum hz hα d e hp)
  · obtain ⟨α,hα,hn⟩ := normalize_root_coefficient z 3 (by decide) hb
    have hA' : rootCoefficientA (scaleConfiguration α z) = 0 := by
      rw [rootCoefficientA_scale, hA, zero_mul]
    let c := (rootPolynomial (scaleConfiguration α z)).coeff 2
    let d := (rootPolynomial (scaleConfiguration α z)).coeff 1
    let e := (rootPolynomial (scaleConfiguration α z)).coeff 0
    have hp : rootPolynomial (scaleConfiguration α z) = coefficientSextic 0 1 c d e := by
      simpa only [hA', hn] using
        rootPolynomial_as_sextic (scaleConfiguration α z) (scaled_centered hz α)
    obtain ⟨hc,hd⟩ := Exceptional.ChartII_of_scaled_maximum hz hα c d e hp
    have hc0 : (rootPolynomial z).coeff 2 = 0 := coefficient_zero_of_scaled hα 2 hc
    have hd0 : (rootPolynomial z).coeff 1 = 0 := coefficient_zero_of_scaled hα 1 hd
    exact False.elim (exclude_trinomial
      (trinomial_of_vanishing_coefficients z (global_maximum_centered hz) hA hc0 hd0))

#print axioms global_maximum_A_zero_classification
end N6
