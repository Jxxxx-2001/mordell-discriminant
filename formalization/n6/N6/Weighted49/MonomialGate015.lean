import N6.Weighted49.MonomialGate014
import N6.Weighted49.GateTransfer007
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M121 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M121 = (den_M121 : R)*monVal x mon_M121 := by
  exact monomial_gate x matrix_e matrix_eDen step120Left step120Right den_M082 den_M121 (x 1) vec_M082 vec_M121 mon_M082 mon_M121 (variableMon 1) step120_nonzero step120_scale step120_vector (matrix_e_columns x hWA) (monomial_M082 x hWA) step120_monomial (variableMon_value_1 x)
theorem monomial_M122 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M122 = (den_M122 : R)*monVal x mon_M122 := by
  exact monomial_gate x matrix_e matrix_eDen step121Left step121Right den_M085 den_M122 (x 1) vec_M085 vec_M122 mon_M085 mon_M122 (variableMon 1) step121_nonzero step121_scale step121_vector (matrix_e_columns x hWA) (monomial_M085 x hWA) step121_monomial (variableMon_value_1 x)
theorem monomial_M123 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M123 = (den_M123 : R)*monVal x mon_M123 := by
  exact monomial_gate x matrix_e matrix_eDen step122Left step122Right den_M088 den_M123 (x 1) vec_M088 vec_M123 mon_M088 mon_M123 (variableMon 1) step122_nonzero step122_scale step122_vector (matrix_e_columns x hWA) (monomial_M088 x hWA) step122_monomial (variableMon_value_1 x)
theorem monomial_M124 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M124 = (den_M124 : R)*monVal x mon_M124 := by
  exact monomial_gate x matrix_e matrix_eDen step123Left step123Right den_M089 den_M124 (x 1) vec_M089 vec_M124 mon_M089 mon_M124 (variableMon 1) step123_nonzero step123_scale step123_vector (matrix_e_columns x hWA) (monomial_M089 x hWA) step123_monomial (variableMon_value_1 x)
theorem monomial_M125 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M125 = (den_M125 : R)*monVal x mon_M125 := by
  exact monomial_gate x matrix_e matrix_eDen step124Left step124Right den_M090 den_M125 (x 1) vec_M090 vec_M125 mon_M090 mon_M125 (variableMon 1) step124_nonzero step124_scale step124_vector (matrix_e_columns x hWA) (monomial_M090 x hWA) step124_monomial (variableMon_value_1 x)
theorem monomial_M126 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M126 = (den_M126 : R)*monVal x mon_M126 := by
  exact monomial_gate x matrix_e matrix_eDen step125Left step125Right den_M091 den_M126 (x 1) vec_M091 vec_M126 mon_M091 mon_M126 (variableMon 1) step125_nonzero step125_scale step125_vector (matrix_e_columns x hWA) (monomial_M091 x hWA) step125_monomial (variableMon_value_1 x)
theorem monomial_M127 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M127 = (den_M127 : R)*monVal x mon_M127 := by
  exact monomial_gate x matrix_e matrix_eDen step126Left step126Right den_M092 den_M127 (x 1) vec_M092 vec_M127 mon_M092 mon_M127 (variableMon 1) step126_nonzero step126_scale step126_vector (matrix_e_columns x hWA) (monomial_M092 x hWA) step126_monomial (variableMon_value_1 x)
theorem monomial_M128 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M128 = (den_M128 : R)*monVal x mon_M128 := by
  exact monomial_gate x matrix_e matrix_eDen step127Left step127Right den_M101 den_M128 (x 1) vec_M101 vec_M128 mon_M101 mon_M128 (variableMon 1) step127_nonzero step127_scale step127_vector (matrix_e_columns x hWA) (monomial_M101 x hWA) step127_monomial (variableMon_value_1 x)
end N6.Weighted49
