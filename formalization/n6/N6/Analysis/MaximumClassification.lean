import N6.Analysis.AZeroClassification
import N6.ExceptionalA1.FromMaximum
import N6.Even.FromMaximum
import N6.BranchEval.GeneralFromMaximum

set_option autoImplicit false

namespace N6

theorem global_maximum_classification {z : Configuration} (hz : IsGlobalMaximum z) :
    IsCenteredPentagon z := by
  by_cases hA : rootCoefficientA z = 0
  · exact global_maximum_A_zero_classification hz hA
  · obtain ⟨α,hα,hA1⟩ := exists_normalize_coefficientA z hA
    let w := scaleConfiguration α z
    let b := (rootPolynomial w).coeff 3
    let c := (rootPolynomial w).coeff 2
    let d := (rootPolynomial w).coeff 1
    let e := (rootPolynomial w).coeff 0
    have hp : rootPolynomial w = coefficientSextic 1 b c d e :=
      normalized_rootPolynomial_as_sextic w (scaled_centered hz α) hA1
    by_cases hb : b = 0
    · have hp0 : rootPolynomial w = coefficientSextic 1 0 c d e := by rwa [hb] at hp
      have hd := ExceptionalA1.scaled_maximum_b_zero_d_zero hz hα c d e hp0
      have hpeven : rootPolynomial w = coefficientSextic 1 0 c 0 e := by rwa [hd] at hp0
      exact False.elim (Even.even_scaled_maximum_impossible hz hα c e hpeven)
    · exact False.elim
        (BranchEval.generic_scaled_maximum_impossible hz hα hA1 b c d e hb hp)

#print axioms global_maximum_classification
end N6
