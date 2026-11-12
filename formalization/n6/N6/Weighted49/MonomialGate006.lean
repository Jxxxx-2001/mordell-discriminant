import N6.Weighted49.MonomialGate005
import N6.Weighted49.GateTransfer003
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M049 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M049 = (den_M049 : R)*monVal x mon_M049 := by
  exact monomial_gate x matrix_c matrix_cDen step048Left step048Right den_M026 den_M049 (x 3) vec_M026 vec_M049 mon_M026 mon_M049 (variableMon 3) step048_nonzero step048_scale step048_vector (matrix_c_columns x hWA) (monomial_M026 x hWA) step048_monomial (variableMon_value_3 x)
theorem monomial_M050 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M050 = (den_M050 : R)*monVal x mon_M050 := by
  exact monomial_gate x matrix_c matrix_cDen step049Left step049Right den_M027 den_M050 (x 3) vec_M027 vec_M050 mon_M027 mon_M050 (variableMon 3) step049_nonzero step049_scale step049_vector (matrix_c_columns x hWA) (monomial_M027 x hWA) step049_monomial (variableMon_value_3 x)
theorem monomial_M051 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M051 = (den_M051 : R)*monVal x mon_M051 := by
  exact monomial_gate x matrix_c matrix_cDen step050Left step050Right den_M028 den_M051 (x 3) vec_M028 vec_M051 mon_M028 mon_M051 (variableMon 3) step050_nonzero step050_scale step050_vector (matrix_c_columns x hWA) (monomial_M028 x hWA) step050_monomial (variableMon_value_3 x)
theorem monomial_M052 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M052 = (den_M052 : R)*monVal x mon_M052 := by
  exact monomial_gate x matrix_c matrix_cDen step051Left step051Right den_M029 den_M052 (x 3) vec_M029 vec_M052 mon_M029 mon_M052 (variableMon 3) step051_nonzero step051_scale step051_vector (matrix_c_columns x hWA) (monomial_M029 x hWA) step051_monomial (variableMon_value_3 x)
theorem monomial_M053 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M053 = (den_M053 : R)*monVal x mon_M053 := by
  exact monomial_gate x matrix_k matrix_kDen step052Left step052Right den_M025 den_M053 (x 2) vec_M025 vec_M053 mon_M025 mon_M053 (variableMon 2) step052_nonzero step052_scale step052_vector (matrix_k_columns x hWA) (monomial_M025 x hWA) step052_monomial (variableMon_value_2 x)
theorem monomial_M054 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M054 = (den_M054 : R)*monVal x mon_M054 := by
  exact monomial_gate x matrix_k matrix_kDen step053Left step053Right den_M026 den_M054 (x 2) vec_M026 vec_M054 mon_M026 mon_M054 (variableMon 2) step053_nonzero step053_scale step053_vector (matrix_k_columns x hWA) (monomial_M026 x hWA) step053_monomial (variableMon_value_2 x)
theorem monomial_M055 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M055 = (den_M055 : R)*monVal x mon_M055 := by
  exact monomial_gate x matrix_k matrix_kDen step054Left step054Right den_M027 den_M055 (x 2) vec_M027 vec_M055 mon_M027 mon_M055 (variableMon 2) step054_nonzero step054_scale step054_vector (matrix_k_columns x hWA) (monomial_M027 x hWA) step054_monomial (variableMon_value_2 x)
theorem monomial_M056 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M056 = (den_M056 : R)*monVal x mon_M056 := by
  exact monomial_gate x matrix_k matrix_kDen step055Left step055Right den_M028 den_M056 (x 2) vec_M028 vec_M056 mon_M028 mon_M056 (variableMon 2) step055_nonzero step055_scale step055_vector (matrix_k_columns x hWA) (monomial_M028 x hWA) step055_monomial (variableMon_value_2 x)
end N6.Weighted49
