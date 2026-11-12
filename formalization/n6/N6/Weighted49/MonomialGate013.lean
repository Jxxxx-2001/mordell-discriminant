import N6.Weighted49.MonomialGate012
import N6.Weighted49.GateTransfer006
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M105 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M105 = (den_M105 : R)*monVal x mon_M105 := by
  exact monomial_gate x matrix_e matrix_eDen step104Left step104Right den_M063 den_M105 (x 1) vec_M063 vec_M105 mon_M063 mon_M105 (variableMon 1) step104_nonzero step104_scale step104_vector (matrix_e_columns x hWA) (monomial_M063 x hWA) step104_monomial (variableMon_value_1 x)
theorem monomial_M106 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M106 = (den_M106 : R)*monVal x mon_M106 := by
  exact monomial_gate x matrix_e matrix_eDen step105Left step105Right den_M064 den_M106 (x 1) vec_M064 vec_M106 mon_M064 mon_M106 (variableMon 1) step105_nonzero step105_scale step105_vector (matrix_e_columns x hWA) (monomial_M064 x hWA) step105_monomial (variableMon_value_1 x)
theorem monomial_M107 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M107 = (den_M107 : R)*monVal x mon_M107 := by
  exact monomial_gate x matrix_e matrix_eDen step106Left step106Right den_M065 den_M107 (x 1) vec_M065 vec_M107 mon_M065 mon_M107 (variableMon 1) step106_nonzero step106_scale step106_vector (matrix_e_columns x hWA) (monomial_M065 x hWA) step106_monomial (variableMon_value_1 x)
theorem monomial_M108 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M108 = (den_M108 : R)*monVal x mon_M108 := by
  exact monomial_gate x matrix_e matrix_eDen step107Left step107Right den_M066 den_M108 (x 1) vec_M066 vec_M108 mon_M066 mon_M108 (variableMon 1) step107_nonzero step107_scale step107_vector (matrix_e_columns x hWA) (monomial_M066 x hWA) step107_monomial (variableMon_value_1 x)
theorem monomial_M109 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M109 = (den_M109 : R)*monVal x mon_M109 := by
  exact monomial_gate x matrix_e matrix_eDen step108Left step108Right den_M070 den_M109 (x 1) vec_M070 vec_M109 mon_M070 mon_M109 (variableMon 1) step108_nonzero step108_scale step108_vector (matrix_e_columns x hWA) (monomial_M070 x hWA) step108_monomial (variableMon_value_1 x)
theorem monomial_M110 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M110 = (den_M110 : R)*monVal x mon_M110 := by
  exact monomial_gate x matrix_e matrix_eDen step109Left step109Right den_M072 den_M110 (x 1) vec_M072 vec_M110 mon_M072 mon_M110 (variableMon 1) step109_nonzero step109_scale step109_vector (matrix_e_columns x hWA) (monomial_M072 x hWA) step109_monomial (variableMon_value_1 x)
theorem monomial_M111 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M111 = (den_M111 : R)*monVal x mon_M111 := by
  exact monomial_gate x matrix_e matrix_eDen step110Left step110Right den_M073 den_M111 (x 1) vec_M073 vec_M111 mon_M073 mon_M111 (variableMon 1) step110_nonzero step110_scale step110_vector (matrix_e_columns x hWA) (monomial_M073 x hWA) step110_monomial (variableMon_value_1 x)
theorem monomial_M112 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M112 = (den_M112 : R)*monVal x mon_M112 := by
  exact monomial_gate x matrix_k matrix_kDen step111Left step111Right den_M081 den_M112 (x 2) vec_M081 vec_M112 mon_M081 mon_M112 (variableMon 2) step111_nonzero step111_scale step111_vector (matrix_k_columns x hWA) (monomial_M081 x hWA) step111_monomial (variableMon_value_2 x)
end N6.Weighted49
