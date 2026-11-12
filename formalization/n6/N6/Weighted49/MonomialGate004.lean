import N6.Weighted49.MonomialGate003
import N6.Weighted49.GateTransfer002
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M033 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M033 = (den_M033 : R)*monVal x mon_M033 := by
  exact monomial_gate x matrix_k matrix_kDen step032Left step032Right den_M015 den_M033 (x 2) vec_M015 vec_M033 mon_M015 mon_M033 (variableMon 2) step032_nonzero step032_scale step032_vector (matrix_k_columns x hWA) (monomial_M015 x hWA) step032_monomial (variableMon_value_2 x)
theorem monomial_M034 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M034 = (den_M034 : R)*monVal x mon_M034 := by
  exact monomial_gate x matrix_k matrix_kDen step033Left step033Right den_M016 den_M034 (x 2) vec_M016 vec_M034 mon_M016 mon_M034 (variableMon 2) step033_nonzero step033_scale step033_vector (matrix_k_columns x hWA) (monomial_M016 x hWA) step033_monomial (variableMon_value_2 x)
theorem monomial_M035 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M035 = (den_M035 : R)*monVal x mon_M035 := by
  exact monomial_gate x matrix_e matrix_eDen step034Left step034Right den_M011 den_M035 (x 1) vec_M011 vec_M035 mon_M011 mon_M035 (variableMon 1) step034_nonzero step034_scale step034_vector (matrix_e_columns x hWA) (monomial_M011 x hWA) step034_monomial (variableMon_value_1 x)
theorem monomial_M036 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M036 = (den_M036 : R)*monVal x mon_M036 := by
  exact monomial_gate x matrix_e matrix_eDen step035Left step035Right den_M012 den_M036 (x 1) vec_M012 vec_M036 mon_M012 mon_M036 (variableMon 1) step035_nonzero step035_scale step035_vector (matrix_e_columns x hWA) (monomial_M012 x hWA) step035_monomial (variableMon_value_1 x)
theorem monomial_M037 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M037 = (den_M037 : R)*monVal x mon_M037 := by
  exact monomial_gate x matrix_e matrix_eDen step036Left step036Right den_M013 den_M037 (x 1) vec_M013 vec_M037 mon_M013 mon_M037 (variableMon 1) step036_nonzero step036_scale step036_vector (matrix_e_columns x hWA) (monomial_M013 x hWA) step036_monomial (variableMon_value_1 x)
theorem monomial_M038 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M038 = (den_M038 : R)*monVal x mon_M038 := by
  exact monomial_gate x matrix_e matrix_eDen step037Left step037Right den_M014 den_M038 (x 1) vec_M014 vec_M038 mon_M014 mon_M038 (variableMon 1) step037_nonzero step037_scale step037_vector (matrix_e_columns x hWA) (monomial_M014 x hWA) step037_monomial (variableMon_value_1 x)
theorem monomial_M039 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M039 = (den_M039 : R)*monVal x mon_M039 := by
  exact monomial_gate x matrix_e matrix_eDen step038Left step038Right den_M015 den_M039 (x 1) vec_M015 vec_M039 mon_M015 mon_M039 (variableMon 1) step038_nonzero step038_scale step038_vector (matrix_e_columns x hWA) (monomial_M015 x hWA) step038_monomial (variableMon_value_1 x)
theorem monomial_M040 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M040 = (den_M040 : R)*monVal x mon_M040 := by
  exact monomial_gate x matrix_e matrix_eDen step039Left step039Right den_M016 den_M040 (x 1) vec_M016 vec_M040 mon_M016 mon_M040 (variableMon 1) step039_nonzero step039_scale step039_vector (matrix_e_columns x hWA) (monomial_M016 x hWA) step039_monomial (variableMon_value_1 x)
end N6.Weighted49
