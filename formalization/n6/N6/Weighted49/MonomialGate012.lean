import N6.Weighted49.MonomialGate011
import N6.Weighted49.GateTransfer006
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M097 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M097 = (den_M097 : R)*monVal x mon_M097 := by
  exact monomial_gate x matrix_e matrix_eDen step096Left step096Right den_M055 den_M097 (x 1) vec_M055 vec_M097 mon_M055 mon_M097 (variableMon 1) step096_nonzero step096_scale step096_vector (matrix_e_columns x hWA) (monomial_M055 x hWA) step096_monomial (variableMon_value_1 x)
theorem monomial_M098 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M098 = (den_M098 : R)*monVal x mon_M098 := by
  exact monomial_gate x matrix_e matrix_eDen step097Left step097Right den_M056 den_M098 (x 1) vec_M056 vec_M098 mon_M056 mon_M098 (variableMon 1) step097_nonzero step097_scale step097_vector (matrix_e_columns x hWA) (monomial_M056 x hWA) step097_monomial (variableMon_value_1 x)
theorem monomial_M099 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M099 = (den_M099 : R)*monVal x mon_M099 := by
  exact monomial_gate x matrix_e matrix_eDen step098Left step098Right den_M057 den_M099 (x 1) vec_M057 vec_M099 mon_M057 mon_M099 (variableMon 1) step098_nonzero step098_scale step098_vector (matrix_e_columns x hWA) (monomial_M057 x hWA) step098_monomial (variableMon_value_1 x)
theorem monomial_M100 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M100 = (den_M100 : R)*monVal x mon_M100 := by
  exact monomial_gate x matrix_e matrix_eDen step099Left step099Right den_M058 den_M100 (x 1) vec_M058 vec_M100 mon_M058 mon_M100 (variableMon 1) step099_nonzero step099_scale step099_vector (matrix_e_columns x hWA) (monomial_M058 x hWA) step099_monomial (variableMon_value_1 x)
theorem monomial_M101 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M101 = (den_M101 : R)*monVal x mon_M101 := by
  exact monomial_gate x matrix_e matrix_eDen step100Left step100Right den_M059 den_M101 (x 1) vec_M059 vec_M101 mon_M059 mon_M101 (variableMon 1) step100_nonzero step100_scale step100_vector (matrix_e_columns x hWA) (monomial_M059 x hWA) step100_monomial (variableMon_value_1 x)
theorem monomial_M102 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M102 = (den_M102 : R)*monVal x mon_M102 := by
  exact monomial_gate x matrix_e matrix_eDen step101Left step101Right den_M060 den_M102 (x 1) vec_M060 vec_M102 mon_M060 mon_M102 (variableMon 1) step101_nonzero step101_scale step101_vector (matrix_e_columns x hWA) (monomial_M060 x hWA) step101_monomial (variableMon_value_1 x)
theorem monomial_M103 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M103 = (den_M103 : R)*monVal x mon_M103 := by
  exact monomial_gate x matrix_e matrix_eDen step102Left step102Right den_M061 den_M103 (x 1) vec_M061 vec_M103 mon_M061 mon_M103 (variableMon 1) step102_nonzero step102_scale step102_vector (matrix_e_columns x hWA) (monomial_M061 x hWA) step102_monomial (variableMon_value_1 x)
theorem monomial_M104 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M104 = (den_M104 : R)*monVal x mon_M104 := by
  exact monomial_gate x matrix_e matrix_eDen step103Left step103Right den_M062 den_M104 (x 1) vec_M062 vec_M104 mon_M062 mon_M104 (variableMon 1) step103_nonzero step103_scale step103_vector (matrix_e_columns x hWA) (monomial_M062 x hWA) step103_monomial (variableMon_value_1 x)
end N6.Weighted49
