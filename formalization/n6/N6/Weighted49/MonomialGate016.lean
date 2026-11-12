import N6.Weighted49.MonomialGate015
import N6.Weighted49.GateTransfer008
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M129 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M129 = (den_M129 : R)*monVal x mon_M129 := by
  exact monomial_gate x matrix_e matrix_eDen step128Left step128Right den_M102 den_M129 (x 1) vec_M102 vec_M129 mon_M102 mon_M129 (variableMon 1) step128_nonzero step128_scale step128_vector (matrix_e_columns x hWA) (monomial_M102 x hWA) step128_monomial (variableMon_value_1 x)
theorem monomial_M130 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M130 = (den_M130 : R)*monVal x mon_M130 := by
  exact monomial_gate x matrix_k matrix_kDen step129Left step129Right den_M112 den_M130 (x 2) vec_M112 vec_M130 mon_M112 mon_M130 (variableMon 2) step129_nonzero step129_scale step129_vector (matrix_k_columns x hWA) (monomial_M112 x hWA) step129_monomial (variableMon_value_2 x)
theorem monomial_M131 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M131 = (den_M131 : R)*monVal x mon_M131 := by
  exact monomial_gate x matrix_k matrix_kDen step130Left step130Right den_M114 den_M131 (x 2) vec_M114 vec_M131 mon_M114 mon_M131 (variableMon 2) step130_nonzero step130_scale step130_vector (matrix_k_columns x hWA) (monomial_M114 x hWA) step130_monomial (variableMon_value_2 x)
theorem monomial_M132 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M132 = (den_M132 : R)*monVal x mon_M132 := by
  exact monomial_gate x matrix_k matrix_kDen step131Left step131Right den_M117 den_M132 (x 2) vec_M117 vec_M132 mon_M117 mon_M132 (variableMon 2) step131_nonzero step131_scale step131_vector (matrix_k_columns x hWA) (monomial_M117 x hWA) step131_monomial (variableMon_value_2 x)
theorem monomial_M133 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M133 = (den_M133 : R)*monVal x mon_M133 := by
  exact monomial_gate x matrix_k matrix_kDen step132Left step132Right den_M118 den_M133 (x 2) vec_M118 vec_M133 mon_M118 mon_M133 (variableMon 2) step132_nonzero step132_scale step132_vector (matrix_k_columns x hWA) (monomial_M118 x hWA) step132_monomial (variableMon_value_2 x)
theorem monomial_M134 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M134 = (den_M134 : R)*monVal x mon_M134 := by
  exact monomial_gate x matrix_k matrix_kDen step133Left step133Right den_M119 den_M134 (x 2) vec_M119 vec_M134 mon_M119 mon_M134 (variableMon 2) step133_nonzero step133_scale step133_vector (matrix_k_columns x hWA) (monomial_M119 x hWA) step133_monomial (variableMon_value_2 x)
theorem monomial_M135 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M135 = (den_M135 : R)*monVal x mon_M135 := by
  exact monomial_gate x matrix_e matrix_eDen step134Left step134Right den_M120 den_M135 (x 1) vec_M120 vec_M135 mon_M120 mon_M135 (variableMon 1) step134_nonzero step134_scale step134_vector (matrix_e_columns x hWA) (monomial_M120 x hWA) step134_monomial (variableMon_value_1 x)
theorem monomial_M136 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M136 = (den_M136 : R)*monVal x mon_M136 := by
  exact monomial_gate x matrix_k matrix_kDen step135Left step135Right den_M134 den_M136 (x 2) vec_M134 vec_M136 mon_M134 mon_M136 (variableMon 2) step135_nonzero step135_scale step135_vector (matrix_k_columns x hWA) (monomial_M134 x hWA) step135_monomial (variableMon_value_2 x)
end N6.Weighted49
