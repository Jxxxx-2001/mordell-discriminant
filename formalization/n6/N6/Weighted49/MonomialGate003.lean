import N6.Weighted49.MonomialGate002
import N6.Weighted49.GateTransfer001
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M025 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M025 = (den_M025 : R)*monVal x mon_M025 := by
  exact monomial_gate x matrix_B matrix_BDen step024Left step024Right den_M011 den_M025 (x 4) vec_M011 vec_M025 mon_M011 mon_M025 (variableMon 4) step024_nonzero step024_scale step024_vector (matrix_B_columns x hWA) (monomial_M011 x hWA) step024_monomial (variableMon_value_4 x)
theorem monomial_M026 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M026 = (den_M026 : R)*monVal x mon_M026 := by
  exact monomial_gate x matrix_c matrix_cDen step025Left step025Right den_M011 den_M026 (x 3) vec_M011 vec_M026 mon_M011 mon_M026 (variableMon 3) step025_nonzero step025_scale step025_vector (matrix_c_columns x hWA) (monomial_M011 x hWA) step025_monomial (variableMon_value_3 x)
theorem monomial_M027 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M027 = (den_M027 : R)*monVal x mon_M027 := by
  exact monomial_gate x matrix_c matrix_cDen step026Left step026Right den_M012 den_M027 (x 3) vec_M012 vec_M027 mon_M012 mon_M027 (variableMon 3) step026_nonzero step026_scale step026_vector (matrix_c_columns x hWA) (monomial_M012 x hWA) step026_monomial (variableMon_value_3 x)
theorem monomial_M028 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M028 = (den_M028 : R)*monVal x mon_M028 := by
  exact monomial_gate x matrix_c matrix_cDen step027Left step027Right den_M013 den_M028 (x 3) vec_M013 vec_M028 mon_M013 mon_M028 (variableMon 3) step027_nonzero step027_scale step027_vector (matrix_c_columns x hWA) (monomial_M013 x hWA) step027_monomial (variableMon_value_3 x)
theorem monomial_M029 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M029 = (den_M029 : R)*monVal x mon_M029 := by
  exact monomial_gate x matrix_c matrix_cDen step028Left step028Right den_M014 den_M029 (x 3) vec_M014 vec_M029 mon_M014 mon_M029 (variableMon 3) step028_nonzero step028_scale step028_vector (matrix_c_columns x hWA) (monomial_M014 x hWA) step028_monomial (variableMon_value_3 x)
theorem monomial_M030 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M030 = (den_M030 : R)*monVal x mon_M030 := by
  exact monomial_gate x matrix_k matrix_kDen step029Left step029Right den_M011 den_M030 (x 2) vec_M011 vec_M030 mon_M011 mon_M030 (variableMon 2) step029_nonzero step029_scale step029_vector (matrix_k_columns x hWA) (monomial_M011 x hWA) step029_monomial (variableMon_value_2 x)
theorem monomial_M031 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M031 = (den_M031 : R)*monVal x mon_M031 := by
  exact monomial_gate x matrix_k matrix_kDen step030Left step030Right den_M012 den_M031 (x 2) vec_M012 vec_M031 mon_M012 mon_M031 (variableMon 2) step030_nonzero step030_scale step030_vector (matrix_k_columns x hWA) (monomial_M012 x hWA) step030_monomial (variableMon_value_2 x)
theorem monomial_M032 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M032 = (den_M032 : R)*monVal x mon_M032 := by
  exact monomial_gate x matrix_k matrix_kDen step031Left step031Right den_M013 den_M032 (x 2) vec_M013 vec_M032 mon_M013 mon_M032 (variableMon 2) step031_nonzero step031_scale step031_vector (matrix_k_columns x hWA) (monomial_M013 x hWA) step031_monomial (variableMon_value_2 x)
end N6.Weighted49
