import N6.Weighted49.MonomialGate001
import N6.Weighted49.GateTransfer001
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M017 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M017 = (den_M017 : R)*monVal x mon_M017 := by
  exact monomial_gate x matrix_k matrix_kDen step016Left step016Right den_M007 den_M017 (x 2) vec_M007 vec_M017 mon_M007 mon_M017 (variableMon 2) step016_nonzero step016_scale step016_vector (matrix_k_columns x hWA) (monomial_M007 x hWA) step016_monomial (variableMon_value_2 x)
theorem monomial_M018 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M018 = (den_M018 : R)*monVal x mon_M018 := by
  exact monomial_gate x matrix_e matrix_eDen step017Left step017Right den_M004 den_M018 (x 1) vec_M004 vec_M018 mon_M004 mon_M018 (variableMon 1) step017_nonzero step017_scale step017_vector (matrix_e_columns x hWA) (monomial_M004 x hWA) step017_monomial (variableMon_value_1 x)
theorem monomial_M019 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M019 = (den_M019 : R)*monVal x mon_M019 := by
  exact monomial_gate x matrix_e matrix_eDen step018Left step018Right den_M005 den_M019 (x 1) vec_M005 vec_M019 mon_M005 mon_M019 (variableMon 1) step018_nonzero step018_scale step018_vector (matrix_e_columns x hWA) (monomial_M005 x hWA) step018_monomial (variableMon_value_1 x)
theorem monomial_M020 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M020 = (den_M020 : R)*monVal x mon_M020 := by
  exact monomial_gate x matrix_e matrix_eDen step019Left step019Right den_M006 den_M020 (x 1) vec_M006 vec_M020 mon_M006 mon_M020 (variableMon 1) step019_nonzero step019_scale step019_vector (matrix_e_columns x hWA) (monomial_M006 x hWA) step019_monomial (variableMon_value_1 x)
theorem monomial_M021 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M021 = (den_M021 : R)*monVal x mon_M021 := by
  exact monomial_gate x matrix_e matrix_eDen step020Left step020Right den_M007 den_M021 (x 1) vec_M007 vec_M021 mon_M007 mon_M021 (variableMon 1) step020_nonzero step020_scale step020_vector (matrix_e_columns x hWA) (monomial_M007 x hWA) step020_monomial (variableMon_value_1 x)
theorem monomial_M022 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M022 = (den_M022 : R)*monVal x mon_M022 := by
  exact monomial_gate x matrix_e matrix_eDen step021Left step021Right den_M008 den_M022 (x 1) vec_M008 vec_M022 mon_M008 mon_M022 (variableMon 1) step021_nonzero step021_scale step021_vector (matrix_e_columns x hWA) (monomial_M008 x hWA) step021_monomial (variableMon_value_1 x)
theorem monomial_M023 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M023 = (den_M023 : R)*monVal x mon_M023 := by
  exact monomial_gate x matrix_e matrix_eDen step022Left step022Right den_M009 den_M023 (x 1) vec_M009 vec_M023 mon_M009 mon_M023 (variableMon 1) step022_nonzero step022_scale step022_vector (matrix_e_columns x hWA) (monomial_M009 x hWA) step022_monomial (variableMon_value_1 x)
theorem monomial_M024 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M024 = (den_M024 : R)*monVal x mon_M024 := by
  exact monomial_gate x matrix_e matrix_eDen step023Left step023Right den_M010 den_M024 (x 1) vec_M010 vec_M024 mon_M010 mon_M024 (variableMon 1) step023_nonzero step023_scale step023_vector (matrix_e_columns x hWA) (monomial_M010 x hWA) step023_monomial (variableMon_value_1 x)
end N6.Weighted49
