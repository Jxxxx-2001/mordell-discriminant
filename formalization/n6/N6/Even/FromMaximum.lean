import N6.Even.PhysicalValue
import N6.Analysis.GenericValue

set_option autoImplicit false
namespace N6.Even
open ProgramData

/-- A nonsingular normalized even sextic cannot represent a six-point global maximum. -/
theorem even_scaled_maximum_impossible {z : N6.Configuration}
    (hz : N6.IsGlobalMaximum z) {α : ℂ} (hα : α ≠ 0) (c e : ℂ)
    (hp : N6.rootPolynomial (N6.scaleConfiguration α z) =
      N6.coefficientSextic 1 0 c 0 e) : False := by
  have hD : actualD c e=N6.complexDiscriminant (N6.scaleConfiguration α z) :=
    (actualD_chart c e).trans
      (N6.ResultantMinors.originalD_eq_discriminant (N6.scaled_dualStationaryPair hz hα)
        0 c 0 e hp)
  have hv : N6.discriminant z^2 =
      (N6.physicalScalar (N6.scaleConfiguration α z))^15*
        Complex.normSq (actualD c e)/(5^30 : ℝ) := by
    rw [hD]
    exact N6.GenericValue.discriminant_sq_normalized z hz.1 α hα
  have bound := even_scaled_maximum_value_bound hz hα c e hp
  exact (N6.GenericValue.not_globalMaximum_of_sq_lt z _ hv bound) hz

#print axioms even_scaled_maximum_impossible
end N6.Even
