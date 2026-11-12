import N6.Weighted49.MonomialGate013
import N6.Weighted49.GateTransfer007
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M113 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M113 = (den_M113 : R)*monVal x mon_M113 := by
  exact monomial_gate x matrix_k matrix_kDen step112Left step112Right den_M083 den_M113 (x 2) vec_M083 vec_M113 mon_M083 mon_M113 (variableMon 2) step112_nonzero step112_scale step112_vector (matrix_k_columns x hWA) (monomial_M083 x hWA) step112_monomial (variableMon_value_2 x)
theorem monomial_M114 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M114 = (den_M114 : R)*monVal x mon_M114 := by
  exact monomial_gate x matrix_k matrix_kDen step113Left step113Right den_M084 den_M114 (x 2) vec_M084 vec_M114 mon_M084 mon_M114 (variableMon 2) step113_nonzero step113_scale step113_vector (matrix_k_columns x hWA) (monomial_M084 x hWA) step113_monomial (variableMon_value_2 x)
theorem monomial_M115 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M115 = (den_M115 : R)*monVal x mon_M115 := by
  exact monomial_gate x matrix_k matrix_kDen step114Left step114Right den_M085 den_M115 (x 2) vec_M085 vec_M115 mon_M085 mon_M115 (variableMon 2) step114_nonzero step114_scale step114_vector (matrix_k_columns x hWA) (monomial_M085 x hWA) step114_monomial (variableMon_value_2 x)
theorem monomial_M116 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M116 = (den_M116 : R)*monVal x mon_M116 := by
  exact monomial_gate x matrix_k matrix_kDen step115Left step115Right den_M086 den_M116 (x 2) vec_M086 vec_M116 mon_M086 mon_M116 (variableMon 2) step115_nonzero step115_scale step115_vector (matrix_k_columns x hWA) (monomial_M086 x hWA) step115_monomial (variableMon_value_2 x)
theorem monomial_M117 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M117 = (den_M117 : R)*monVal x mon_M117 := by
  exact monomial_gate x matrix_k matrix_kDen step116Left step116Right den_M087 den_M117 (x 2) vec_M087 vec_M117 mon_M087 mon_M117 (variableMon 2) step116_nonzero step116_scale step116_vector (matrix_k_columns x hWA) (monomial_M087 x hWA) step116_monomial (variableMon_value_2 x)
theorem monomial_M118 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M118 = (den_M118 : R)*monVal x mon_M118 := by
  exact monomial_gate x matrix_k matrix_kDen step117Left step117Right den_M088 den_M118 (x 2) vec_M088 vec_M118 mon_M088 mon_M118 (variableMon 2) step117_nonzero step117_scale step117_vector (matrix_k_columns x hWA) (monomial_M088 x hWA) step117_monomial (variableMon_value_2 x)
theorem monomial_M119 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M119 = (den_M119 : R)*monVal x mon_M119 := by
  exact monomial_gate x matrix_k matrix_kDen step118Left step118Right den_M090 den_M119 (x 2) vec_M090 vec_M119 mon_M090 mon_M119 (variableMon 2) step118_nonzero step118_scale step118_vector (matrix_k_columns x hWA) (monomial_M090 x hWA) step118_monomial (variableMon_value_2 x)
theorem monomial_M120 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M120 = (den_M120 : R)*monVal x mon_M120 := by
  exact monomial_gate x matrix_k matrix_kDen step119Left step119Right den_M091 den_M120 (x 2) vec_M091 vec_M120 mon_M091 mon_M120 (variableMon 2) step119_nonzero step119_scale step119_vector (matrix_k_columns x hWA) (monomial_M091 x hWA) step119_monomial (variableMon_value_2 x)
end N6.Weighted49
