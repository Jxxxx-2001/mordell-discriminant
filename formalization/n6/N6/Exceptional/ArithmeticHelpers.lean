import N6.Exceptional.Data
import review.SparseProductReduce
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Tactic.LinearCombination
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
set_option linter.unusedVariables false
namespace N6.Exceptional
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem value_scaled {R : Type*} [CommRing R] (x : Fin 5 → R) (a : Int) (p : Poly) :
    value x (scaled a p) = (a : R) * value x p := by
  simpa only [scaled, m0000, monVal, pow_zero, mul_one, one_mul] using
    (N6.SparseCheck.value_mapMul x (m0000,a) p)
theorem value_one {R : Type*} [CommRing R] (x : Fin 5 → R) : value x one = (1 : R) := by
  simp only [one, value, m0000, monVal, pow_zero, Int.cast_one, mul_one, one_mul, add_zero]
theorem value_D000 {R : Type*} [CommRing R] (x : Fin 5 → R) : value x D000 = (1 : R) := by
  simpa only [D000] using value_one x
theorem value_J000 {R : Type*} [CommRing R] (x : Fin 5 → R) : value x J000 = (0 : R) := rfl
#print axioms value_scaled
#print axioms value_one
end N6.Exceptional
