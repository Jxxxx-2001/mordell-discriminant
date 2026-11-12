import Mathlib.Tactic.FinCases
import N6.Certificate
import N6.Weighted49.ParentData
import review.SparseProductReduce
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem value_scalar {R : Type*} [CommRing R] (x : Fin 5 → R) (z : Int) : value x (scalar z) = (z : R) := by simp [scalar, value, monVal]
theorem value_basis {R : Type*} [CommRing R] (x : Fin 5 → R) (i : Fin 49) : value x (basisData i) = monVal x (basisMon i) := by simp [basisData, value]
end N6.Weighted49
