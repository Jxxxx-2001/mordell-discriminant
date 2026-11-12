import N6.Weighted49.GateSemanticsHelpers
import N6.Weighted49.GateTransfer000
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M000 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M000 = (den_M000 : R) * monVal x mon_M000 := by
  simp [W, unitVectorChecked, value_basis, basisMon, mon_M000, monVal, den_M000]
end N6.Weighted49
