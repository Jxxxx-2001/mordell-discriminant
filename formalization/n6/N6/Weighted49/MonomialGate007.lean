import N6.Weighted49.MonomialGate006
import N6.Weighted49.GateTransfer003
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M057 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M057 = (den_M057 : R)*monVal x mon_M057 := by
  exact monomial_gate x matrix_k matrix_kDen step056Left step056Right den_M030 den_M057 (x 2) vec_M030 vec_M057 mon_M030 mon_M057 (variableMon 2) step056_nonzero step056_scale step056_vector (matrix_k_columns x hWA) (monomial_M030 x hWA) step056_monomial (variableMon_value_2 x)
theorem monomial_M058 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M058 = (den_M058 : R)*monVal x mon_M058 := by
  exact monomial_gate x matrix_k matrix_kDen step057Left step057Right den_M031 den_M058 (x 2) vec_M031 vec_M058 mon_M031 mon_M058 (variableMon 2) step057_nonzero step057_scale step057_vector (matrix_k_columns x hWA) (monomial_M031 x hWA) step057_monomial (variableMon_value_2 x)
theorem monomial_M059 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M059 = (den_M059 : R)*monVal x mon_M059 := by
  exact monomial_gate x matrix_k matrix_kDen step058Left step058Right den_M032 den_M059 (x 2) vec_M032 vec_M059 mon_M032 mon_M059 (variableMon 2) step058_nonzero step058_scale step058_vector (matrix_k_columns x hWA) (monomial_M032 x hWA) step058_monomial (variableMon_value_2 x)
theorem monomial_M060 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M060 = (den_M060 : R)*monVal x mon_M060 := by
  exact monomial_gate x matrix_k matrix_kDen step059Left step059Right den_M033 den_M060 (x 2) vec_M033 vec_M060 mon_M033 mon_M060 (variableMon 2) step059_nonzero step059_scale step059_vector (matrix_k_columns x hWA) (monomial_M033 x hWA) step059_monomial (variableMon_value_2 x)
theorem monomial_M061 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M061 = (den_M061 : R)*monVal x mon_M061 := by
  exact monomial_gate x matrix_e matrix_eDen step060Left step060Right den_M028 den_M061 (x 1) vec_M028 vec_M061 mon_M028 mon_M061 (variableMon 1) step060_nonzero step060_scale step060_vector (matrix_e_columns x hWA) (monomial_M028 x hWA) step060_monomial (variableMon_value_1 x)
theorem monomial_M062 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M062 = (den_M062 : R)*monVal x mon_M062 := by
  exact monomial_gate x matrix_e matrix_eDen step061Left step061Right den_M029 den_M062 (x 1) vec_M029 vec_M062 mon_M029 mon_M062 (variableMon 1) step061_nonzero step061_scale step061_vector (matrix_e_columns x hWA) (monomial_M029 x hWA) step061_monomial (variableMon_value_1 x)
theorem monomial_M063 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M063 = (den_M063 : R)*monVal x mon_M063 := by
  exact monomial_gate x matrix_e matrix_eDen step062Left step062Right den_M031 den_M063 (x 1) vec_M031 vec_M063 mon_M031 mon_M063 (variableMon 1) step062_nonzero step062_scale step062_vector (matrix_e_columns x hWA) (monomial_M031 x hWA) step062_monomial (variableMon_value_1 x)
theorem monomial_M064 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M064 = (den_M064 : R)*monVal x mon_M064 := by
  exact monomial_gate x matrix_e matrix_eDen step063Left step063Right den_M032 den_M064 (x 1) vec_M032 vec_M064 mon_M032 mon_M064 (variableMon 1) step063_nonzero step063_scale step063_vector (matrix_e_columns x hWA) (monomial_M032 x hWA) step063_monomial (variableMon_value_1 x)
end N6.Weighted49
