import N6.Weighted49.MonomialGate016
import N6.Weighted49.InitTransfer
import N6.Weighted49.ColumnHelpers
import Mathlib.Data.Fintype.Fin
import Mathlib.Tactic.LinearCombination
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem original_D_sum {R : Type*} [CommRing R] (x : Fin 5 → R) :
    (∑ j : Fin 76, (initCoefficients j : R)*monVal x (initMons j)) = value x N6.Dcolon1.dData := by
  have h := N6.SparseProductReduce.pairs_vanish x initDPairs initDChecked
  simp only [initDPairs, pairs, value_scalar, Int.cast_one, Int.cast_neg, one_mul, neg_mul, add_zero] at h
  have hD : value x initPoly = value x N6.Dcolon1.dData := by linear_combination h
  simpa only [initPoly, value_polyLin, W] using hD
theorem D_initialization {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K000 = (den_K000 : R)*value x N6.Dcolon1.dData := by
  have sources : ∀ j : Fin 76, W (fun i => value x (basisData i)) (initSource j) = (initDens j : R)*monVal x (initMons j) := by
    intro j
    fin_cases j
    · simpa only [initSource, initDens, initMons] using monomial_M116 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M113 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M096 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M132 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M117 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M067 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M125 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M099 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M136 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M134 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M119 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M090 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M093 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M131 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M114 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M123 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M097 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M133 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M118 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M088 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M105 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M068 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M135 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M126 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M100 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M063 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M120 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M091 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M074 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M129 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M107 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M071 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M042 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M127 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M102 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M065 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M092 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M130 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M122 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M094 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M115 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M103 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M124 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M098 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M061 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M089 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M128 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M106 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M069 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M101 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M064 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M110 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M075 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M108 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M072 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M043 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M066 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M078 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M111 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M077 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M046 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M073 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M045 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M121 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M095 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M104 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M062 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M109 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M070 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M076 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M044 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M079 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M047 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M080 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M048 x hWA
    · simpa only [initSource, initDens, initMons] using monomial_M024 x hWA
  have h := sum_gate (fun i => value x (basisData i)) initWeights initDens initCoefficients initSource (fun j => monVal x (initMons j)) vec_K000 step136Left den_K000 initClearing_nonzero initVectorChecked initWeightsChecked sources
  rw [original_D_sum x] at h
  exact h
#print axioms D_initialization
end N6.Weighted49
