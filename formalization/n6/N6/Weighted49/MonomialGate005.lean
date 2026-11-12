import N6.Weighted49.MonomialGate004
import N6.Weighted49.GateTransfer002
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M041 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M041 = (den_M041 : R)*monVal x mon_M041 := by
  exact monomial_gate x matrix_e matrix_eDen step040Left step040Right den_M017 den_M041 (x 1) vec_M017 vec_M041 mon_M017 mon_M041 (variableMon 1) step040_nonzero step040_scale step040_vector (matrix_e_columns x hWA) (monomial_M017 x hWA) step040_monomial (variableMon_value_1 x)
theorem monomial_M042 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M042 = (den_M042 : R)*monVal x mon_M042 := by
  exact monomial_gate x matrix_e matrix_eDen step041Left step041Right den_M018 den_M042 (x 1) vec_M018 vec_M042 mon_M018 mon_M042 (variableMon 1) step041_nonzero step041_scale step041_vector (matrix_e_columns x hWA) (monomial_M018 x hWA) step041_monomial (variableMon_value_1 x)
theorem monomial_M043 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M043 = (den_M043 : R)*monVal x mon_M043 := by
  exact monomial_gate x matrix_e matrix_eDen step042Left step042Right den_M019 den_M043 (x 1) vec_M019 vec_M043 mon_M019 mon_M043 (variableMon 1) step042_nonzero step042_scale step042_vector (matrix_e_columns x hWA) (monomial_M019 x hWA) step042_monomial (variableMon_value_1 x)
theorem monomial_M044 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M044 = (den_M044 : R)*monVal x mon_M044 := by
  exact monomial_gate x matrix_e matrix_eDen step043Left step043Right den_M020 den_M044 (x 1) vec_M020 vec_M044 mon_M020 mon_M044 (variableMon 1) step043_nonzero step043_scale step043_vector (matrix_e_columns x hWA) (monomial_M020 x hWA) step043_monomial (variableMon_value_1 x)
theorem monomial_M045 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M045 = (den_M045 : R)*monVal x mon_M045 := by
  exact monomial_gate x matrix_e matrix_eDen step044Left step044Right den_M021 den_M045 (x 1) vec_M021 vec_M045 mon_M021 mon_M045 (variableMon 1) step044_nonzero step044_scale step044_vector (matrix_e_columns x hWA) (monomial_M021 x hWA) step044_monomial (variableMon_value_1 x)
theorem monomial_M046 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M046 = (den_M046 : R)*monVal x mon_M046 := by
  exact monomial_gate x matrix_e matrix_eDen step045Left step045Right den_M022 den_M046 (x 1) vec_M022 vec_M046 mon_M022 mon_M046 (variableMon 1) step045_nonzero step045_scale step045_vector (matrix_e_columns x hWA) (monomial_M022 x hWA) step045_monomial (variableMon_value_1 x)
theorem monomial_M047 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M047 = (den_M047 : R)*monVal x mon_M047 := by
  exact monomial_gate x matrix_e matrix_eDen step046Left step046Right den_M023 den_M047 (x 1) vec_M023 vec_M047 mon_M023 mon_M047 (variableMon 1) step046_nonzero step046_scale step046_vector (matrix_e_columns x hWA) (monomial_M023 x hWA) step046_monomial (variableMon_value_1 x)
theorem monomial_M048 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M048 = (den_M048 : R)*monVal x mon_M048 := by
  exact monomial_gate x matrix_e matrix_eDen step047Left step047Right den_M024 den_M048 (x 1) vec_M024 vec_M048 mon_M024 mon_M048 (variableMon 1) step047_nonzero step047_scale step047_vector (matrix_e_columns x hWA) (monomial_M024 x hWA) step047_monomial (variableMon_value_1 x)
end N6.Weighted49
