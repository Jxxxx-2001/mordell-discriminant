import N6.Weighted49.MonomialGate008
import N6.Weighted49.GateTransfer004
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M073 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M073 = (den_M073 : R)*monVal x mon_M073 := by
  exact monomial_gate x matrix_e matrix_eDen step072Left step072Right den_M041 den_M073 (x 1) vec_M041 vec_M073 mon_M041 mon_M073 (variableMon 1) step072_nonzero step072_scale step072_vector (matrix_e_columns x hWA) (monomial_M041 x hWA) step072_monomial (variableMon_value_1 x)
theorem monomial_M074 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M074 = (den_M074 : R)*monVal x mon_M074 := by
  exact monomial_gate x matrix_e matrix_eDen step073Left step073Right den_M042 den_M074 (x 1) vec_M042 vec_M074 mon_M042 mon_M074 (variableMon 1) step073_nonzero step073_scale step073_vector (matrix_e_columns x hWA) (monomial_M042 x hWA) step073_monomial (variableMon_value_1 x)
theorem monomial_M075 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M075 = (den_M075 : R)*monVal x mon_M075 := by
  exact monomial_gate x matrix_e matrix_eDen step074Left step074Right den_M043 den_M075 (x 1) vec_M043 vec_M075 mon_M043 mon_M075 (variableMon 1) step074_nonzero step074_scale step074_vector (matrix_e_columns x hWA) (monomial_M043 x hWA) step074_monomial (variableMon_value_1 x)
theorem monomial_M076 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M076 = (den_M076 : R)*monVal x mon_M076 := by
  exact monomial_gate x matrix_e matrix_eDen step075Left step075Right den_M044 den_M076 (x 1) vec_M044 vec_M076 mon_M044 mon_M076 (variableMon 1) step075_nonzero step075_scale step075_vector (matrix_e_columns x hWA) (monomial_M044 x hWA) step075_monomial (variableMon_value_1 x)
theorem monomial_M077 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M077 = (den_M077 : R)*monVal x mon_M077 := by
  exact monomial_gate x matrix_e matrix_eDen step076Left step076Right den_M045 den_M077 (x 1) vec_M045 vec_M077 mon_M045 mon_M077 (variableMon 1) step076_nonzero step076_scale step076_vector (matrix_e_columns x hWA) (monomial_M045 x hWA) step076_monomial (variableMon_value_1 x)
theorem monomial_M078 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M078 = (den_M078 : R)*monVal x mon_M078 := by
  exact monomial_gate x matrix_e matrix_eDen step077Left step077Right den_M046 den_M078 (x 1) vec_M046 vec_M078 mon_M046 mon_M078 (variableMon 1) step077_nonzero step077_scale step077_vector (matrix_e_columns x hWA) (monomial_M046 x hWA) step077_monomial (variableMon_value_1 x)
theorem monomial_M079 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M079 = (den_M079 : R)*monVal x mon_M079 := by
  exact monomial_gate x matrix_e matrix_eDen step078Left step078Right den_M047 den_M079 (x 1) vec_M047 vec_M079 mon_M047 mon_M079 (variableMon 1) step078_nonzero step078_scale step078_vector (matrix_e_columns x hWA) (monomial_M047 x hWA) step078_monomial (variableMon_value_1 x)
theorem monomial_M080 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M080 = (den_M080 : R)*monVal x mon_M080 := by
  exact monomial_gate x matrix_e matrix_eDen step079Left step079Right den_M048 den_M080 (x 1) vec_M048 vec_M080 mon_M048 mon_M080 (variableMon 1) step079_nonzero step079_scale step079_vector (matrix_e_columns x hWA) (monomial_M048 x hWA) step079_monomial (variableMon_value_1 x)
end N6.Weighted49
