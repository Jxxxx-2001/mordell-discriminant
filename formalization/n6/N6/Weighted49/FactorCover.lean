import N6.Weighted49.FactorGround
import N6.Weighted49.LexSemantics
import N6.ResultantMinors.Bindings
import N6.ResultantMinors.ArithmeticHelpers
import Mathlib.Data.Fintype.Fin
set_option maxRecDepth 32000
set_option maxHeartbeats 1000000
namespace N6.Weighted49.FactorCover
open N6.SparseCheck N6.ResultantMinors
open N6.ResultantMinors
open scoped BigOperators
theorem value_ofFn {R : Type*} [CommRing R] (x : Fin 5 → R) {n : Nat} (a : Fin n → Term) :
    value x (List.ofFn a) = ∑ i, ((a i).2 : R) * monVal x (a i).1 := by
  induction n with
  | zero => simp [List.ofFn_zero, value]
  | succ n ih => rw [List.ofFn_succ, value, Fin.sum_univ_succ, ih]

theorem globalData_value {R : Type*} [CommRing R] (B : R) :
    value (point B 0 0 0 0) globalData = globalP35 B := by
  rw [← globalDataBinding, value_ofFn]
  simp only [globalP35, monVal, point_eval0, point_eval1, point_eval2,
    point_eval3, point_eval4, pow_zero, one_mul]

theorem factorization {R : Type*} [CommRing R] (B : R) :
    globalP35 B = value (point B 0 0 0 0) factor0Data *
      value (point B 0 0 0 0) factor1Data * value (point B 0 0 0 0) factor2Data *
      value (point B 0 0 0 0) factor3Data * value (point B 0 0 0 0) factor4Data *
      value (point B 0 0 0 0) factor5Data := by
  have h := value_zero (point B 0 0 0 0) factorChecked
  rw [value_merge, value_scaled, globalData_value] at h
  simp only [Int.cast_neg, Int.cast_one, neg_one_mul] at h
  have he := eq_of_sub_eq_zero (show globalP35 B - value (point B 0 0 0 0) factorProduct = 0 by simpa only [sub_eq_add_neg] using h)
  rw [he]
  simp only [factorProduct, value_mul]
  ring

theorem cover {K : Type*} [Field K] (B : K) (h : globalP35 B = 0) :
    value (point B 0 0 0 0) factor0Data = 0 ∨ value (point B 0 0 0 0) factor1Data = 0 ∨
      value (point B 0 0 0 0) factor2Data = 0 ∨ value (point B 0 0 0 0) factor3Data = 0 ∨
      value (point B 0 0 0 0) factor4Data = 0 ∨ value (point B 0 0 0 0) factor5Data = 0 := by
  rw [factorization] at h
  simpa only [mul_eq_zero, or_assoc] using h
#print axioms factorization
#print axioms cover
end N6.Weighted49.FactorCover
