import N6.ResultantMinors.DeterminantsAll
import review.Resultant6Coefficients

set_option autoImplicit false

namespace N6.ResultantMinors
open N6.SparseCheck Polynomial

theorem stationaryR0_eq_liftY {w y : N6.Configuration}
    (h : N6.DualStationaryPair w y) (b c d e : ℂ)
    (hp : N6.rootPolynomial w = N6.coefficientSextic 1 b c d e) :
    N6.stationaryR0 w y = liftY b c d e D063 := by
  apply Polynomial.funext
  intro U
  have hv := (stationaryResultant_full_jet w h.left_injective b c d e U hp).1
  rw [N6.stationaryResultant_at_zero h U] at hv
  exact hv.trans (eval_liftY b c d e U D063).symm

theorem stationaryRT_eq_liftY {w y : N6.Configuration}
    (h : N6.DualStationaryPair w y) (b c d e : ℂ)
    (hp : N6.rootPolynomial w = N6.coefficientSextic 1 b c d e) :
    N6.stationaryRT w y = liftY b c d e J063 := by
  apply Polynomial.funext
  intro U
  have hd := (stationaryResultant_full_jet w h.left_injective b c d e U hp).2
  have hv := hd.unique (N6.stationaryResultant_hasDerivAt h U)
  exact hv.symm.trans (eval_liftY b c d e U J063).symm

theorem discriminant_coeff_identity {w y : N6.Configuration}
    (h : N6.DualStationaryPair w y) (b c d e : ℂ)
    (hp : N6.rootPolynomial w = N6.coefficientSextic 1 b c d e) :
    N6.complexDiscriminant w =
      value (point b c d e 0) (extractY 6 D063) := by
  rw [← N6.stationaryR0_coeff_six w y, stationaryR0_eq_liftY h b c d e hp,
    coeff_liftY]

#print axioms stationaryR0_eq_liftY
#print axioms stationaryRT_eq_liftY
#print axioms discriminant_coeff_identity
end N6.ResultantMinors
