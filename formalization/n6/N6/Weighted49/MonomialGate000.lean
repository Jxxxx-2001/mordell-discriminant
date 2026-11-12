import N6.Weighted49.MonomialBase
import N6.Weighted49.GateTransfer000
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M001 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M001 = (den_M001 : R)*monVal x mon_M001 := by
  exact monomial_gate x matrix_B matrix_BDen step000Left step000Right den_M000 den_M001 (x 4) vec_M000 vec_M001 mon_M000 mon_M001 (variableMon 4) step000_nonzero step000_scale step000_vector (matrix_B_columns x hWA) (monomial_M000 x hWA) step000_monomial (variableMon_value_4 x)
theorem monomial_M002 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M002 = (den_M002 : R)*monVal x mon_M002 := by
  exact monomial_gate x matrix_c matrix_cDen step001Left step001Right den_M000 den_M002 (x 3) vec_M000 vec_M002 mon_M000 mon_M002 (variableMon 3) step001_nonzero step001_scale step001_vector (matrix_c_columns x hWA) (monomial_M000 x hWA) step001_monomial (variableMon_value_3 x)
theorem monomial_M003 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M003 = (den_M003 : R)*monVal x mon_M003 := by
  exact monomial_gate x matrix_e matrix_eDen step002Left step002Right den_M000 den_M003 (x 1) vec_M000 vec_M003 mon_M000 mon_M003 (variableMon 1) step002_nonzero step002_scale step002_vector (matrix_e_columns x hWA) (monomial_M000 x hWA) step002_monomial (variableMon_value_1 x)
theorem monomial_M004 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M004 = (den_M004 : R)*monVal x mon_M004 := by
  exact monomial_gate x matrix_B matrix_BDen step003Left step003Right den_M001 den_M004 (x 4) vec_M001 vec_M004 mon_M001 mon_M004 (variableMon 4) step003_nonzero step003_scale step003_vector (matrix_B_columns x hWA) (monomial_M001 x hWA) step003_monomial (variableMon_value_4 x)
theorem monomial_M005 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M005 = (den_M005 : R)*monVal x mon_M005 := by
  exact monomial_gate x matrix_c matrix_cDen step004Left step004Right den_M001 den_M005 (x 3) vec_M001 vec_M005 mon_M001 mon_M005 (variableMon 3) step004_nonzero step004_scale step004_vector (matrix_c_columns x hWA) (monomial_M001 x hWA) step004_monomial (variableMon_value_3 x)
theorem monomial_M006 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M006 = (den_M006 : R)*monVal x mon_M006 := by
  exact monomial_gate x matrix_c matrix_cDen step005Left step005Right den_M002 den_M006 (x 3) vec_M002 vec_M006 mon_M002 mon_M006 (variableMon 3) step005_nonzero step005_scale step005_vector (matrix_c_columns x hWA) (monomial_M002 x hWA) step005_monomial (variableMon_value_3 x)
theorem monomial_M007 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M007 = (den_M007 : R)*monVal x mon_M007 := by
  exact monomial_gate x matrix_k matrix_kDen step006Left step006Right den_M001 den_M007 (x 2) vec_M001 vec_M007 mon_M001 mon_M007 (variableMon 2) step006_nonzero step006_scale step006_vector (matrix_k_columns x hWA) (monomial_M001 x hWA) step006_monomial (variableMon_value_2 x)
theorem monomial_M008 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M008 = (den_M008 : R)*monVal x mon_M008 := by
  exact monomial_gate x matrix_e matrix_eDen step007Left step007Right den_M001 den_M008 (x 1) vec_M001 vec_M008 mon_M001 mon_M008 (variableMon 1) step007_nonzero step007_scale step007_vector (matrix_e_columns x hWA) (monomial_M001 x hWA) step007_monomial (variableMon_value_1 x)
end N6.Weighted49
