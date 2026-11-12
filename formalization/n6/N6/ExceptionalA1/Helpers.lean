import N6.ExceptionalA1.Ground
import review.SparseProductReduce
import review.KroneckerFastPack
import Mathlib.Tactic.LinearCombination
set_option maxRecDepth 64000
set_option maxHeartbeats 6000000
set_option linter.unusedVariables false
namespace N6.ExceptionalA1
open N6.SparseCheck N6.KroneckerCheck
variable {K : Type*} [CommRing K]
theorem value_scaled (x : Fin 5 → K) (z : Int) (p : Poly) : value x (scaled z p) = (z : K)*value x p := by
  induction p with
  | nil => simp [scaled, value]
  | cons a p ih => simp only [scaled, List.map_cons, value, Int.cast_mul] at ih ⊢; rw [ih]; ring
theorem value_atBZero (x : Fin 5 → K) (hx : x 4 = 0) (p : Poly) : value x (atBZero p) = value x p := by
  induction p with
  | nil => rfl
  | cons a p ih =>
    by_cases h : a.1.b = 0
    · simpa [atBZero, h, value] using congrArg (fun z : K => (a.2 : K)*monVal x a.1 + z) ih
    · have hm : monVal x a.1 = 0 := by simp [monVal, hx, zero_pow h]
      simpa [atBZero, h, value, hm] using ih
theorem projection_value (x : Fin 5 → K) (hx : x 4 = 0) (p q : Poly)
    (hc : zero (merge (atBZero p) (scaled (-1) q)) = true) : value x q = value x p := by
  have h := value_zero x hc
  rw [value_merge, value_scaled, value_atBZero x hx] at h
  linear_combination -h
theorem goalFactor_value (x : Fin 5 → K) : value x goalFactor = (clearing : K)*(x 2)^3 := by simp [goalFactor, value, monVal]
theorem certificate_identity (x : Fin 5 → K) : N6.KroneckerCheck.pairs (value x) certificatePairs = 0 := by
  apply N6.KroneckerCheck.check x certificateRad certificateBits certificatePairs certificateRoom certificateMass
  exact (N6.KroneckerFastPack.pairs_fastPack_eq certificateRad certificateBits certificateDepth certificatePairs).symm.trans certificateFast
#print axioms certificate_identity
end N6.ExceptionalA1
