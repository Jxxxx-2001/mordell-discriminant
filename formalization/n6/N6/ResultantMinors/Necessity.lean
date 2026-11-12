import N6.ResultantMinors.PolynomialBridge
import N6.ResultantMinors.RawCoefficientBindings
import N6.ResultantMinors.R4Semantics
import N6.Analysis.PhysicalCoefficients

set_option autoImplicit false

namespace N6.ResultantMinors
open N6.SparseCheck Polynomial

theorem originalD_eq_discriminant {w y : N6.Configuration}
    (h : N6.DualStationaryPair w y) (b c d e : ℂ)
    (hp : N6.rootPolynomial w = N6.coefficientSextic 1 b c d e) :
    N6.Chart.originalD b c d e = N6.complexDiscriminant w := by
  rw [discriminant_coeff_identity h b c d e hp]
  exact (actualD_chart b c d e).symm

/-- The literal archived E equations follow from the two stationary force
equations; they are not an independent classification hypothesis. -/
theorem original_equations {w y : N6.Configuration}
    (h : N6.DualStationaryPair w y) (b c d e : ℂ)
    (hp : N6.rootPolynomial w = N6.coefficientSextic 1 b c d e)
    (hr : N6.RawStationaryEquations w y) :
    N6.Chart.E0 b c d e = 0 ∧ N6.Chart.E1 b c d e = 0 ∧
      N6.Chart.E2 b c d e = 0 ∧ N6.Chart.E3 b c d e = 0 := by
  have r0 := stationaryR0_eq_liftY h b c d e hp
  have rt := stationaryRT_eq_liftY h b c d e hp
  rcases hr with ⟨h0, h1, h2, h3⟩
  rw [rt, coeff_liftY] at h0
  rw [rt, r0, coeff_liftY, coeff_liftY] at h1 h2 h3
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [← actualE0_chart]
    exact h0
  · rw [← actualE1_chart]
    simpa only [actualE1Data, value_append, value_scaled,
      Int.cast_neg, Int.cast_ofNat, neg_mul, sub_eq_add_neg] using h1
  · rw [← actualE2_chart]
    simpa only [actualE2Data, value_append, value_scaled,
      Int.cast_neg, Int.cast_ofNat, neg_mul, sub_eq_add_neg] using h2
  · rw [← actualE3_chart]
    simpa only [actualE3Data, value_append, value_scaled,
      Int.cast_neg, Int.cast_ofNat, neg_mul, sub_eq_add_neg] using h3

theorem scaled_maximum_original_equations {z : N6.Configuration}
    (hz : N6.IsGlobalMaximum z) {α : ℂ} (hα : α ≠ 0) (b c d e : ℂ)
    (hp : N6.rootPolynomial (N6.scaleConfiguration α z) =
      N6.coefficientSextic 1 b c d e) :
    N6.Chart.E0 b c d e = 0 ∧ N6.Chart.E1 b c d e = 0 ∧
      N6.Chart.E2 b c d e = 0 ∧ N6.Chart.E3 b c d e = 0 :=
  original_equations (N6.scaled_dualStationaryPair hz hα) b c d e hp
    (N6.scaled_maximum_rawStationaryEquations hz hα)

theorem scaled_maximum_originalD_ne {z : N6.Configuration}
    (hz : N6.IsGlobalMaximum z) {α : ℂ} (hα : α ≠ 0) (b c d e : ℂ)
    (hp : N6.rootPolynomial (N6.scaleConfiguration α z) =
      N6.coefficientSextic 1 b c d e) : N6.Chart.originalD b c d e ≠ 0 := by
  rw [originalD_eq_discriminant (N6.scaled_dualStationaryPair hz hα) b c d e hp]
  exact N6.complexDiscriminant_ne (N6.scaled_injective hz hα)

theorem scaled_maximum_original_r4 {z : N6.Configuration}
    (hz : N6.IsGlobalMaximum z) {α : ℂ} (hα : α ≠ 0)
    (hA : N6.rootCoefficientA (N6.scaleConfiguration α z) = 1)
    (b c d e : ℂ)
    (hp : N6.rootPolynomial (N6.scaleConfiguration α z) =
      N6.coefficientSextic 1 b c d e) :
    value (point b c d e 0) (extractY 4 D063) =
      N6.Chart.originalD b c d e *
        (N6.physicalScalar (N6.scaleConfiguration α z) : ℂ) := by
  rw [← coeff_liftY, ← stationaryR0_eq_liftY (N6.scaled_dualStationaryPair hz hα)
    b c d e hp, N6.scaled_maximum_resultant_four hz hα hA,
    originalD_eq_discriminant (N6.scaled_dualStationaryPair hz hα) b c d e hp]

theorem scaled_maximum_quotient_r4 {z : N6.Configuration}
    (hz : N6.IsGlobalMaximum z) {α : ℂ} (hα : α ≠ 0)
    (hA : N6.rootCoefficientA (N6.scaleConfiguration α z) = 1)
    (b c k e : ℂ)
    (hp : N6.rootPolynomial (N6.scaleConfiguration α z) =
      N6.coefficientSextic 1 b c (b*k) e) :
    value (point (b^2) c k e 0) quotientR4Data =
      N6.Chart.D (b^2) c k e *
        (N6.physicalScalar (N6.scaleConfiguration α z) : ℂ) := by
  rw [← rawR4_substitution]
  simpa only [N6.Chart.discriminant_substitution] using
    scaled_maximum_original_r4 hz hα hA b c (b*k) e hp

#print axioms original_equations
#print axioms scaled_maximum_original_equations
#print axioms scaled_maximum_originalD_ne
#print axioms scaled_maximum_quotient_r4
end N6.ResultantMinors
