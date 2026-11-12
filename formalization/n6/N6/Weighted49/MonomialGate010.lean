import N6.Weighted49.MonomialGate009
import N6.Weighted49.GateTransfer005
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M081 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M081 = (den_M081 : R)*monVal x mon_M081 := by
  exact monomial_gate x matrix_c matrix_cDen step080Left step080Right den_M051 den_M081 (x 3) vec_M051 vec_M081 mon_M051 mon_M081 (variableMon 3) step080_nonzero step080_scale step080_vector (matrix_c_columns x hWA) (monomial_M051 x hWA) step080_monomial (variableMon_value_3 x)
theorem monomial_M082 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M082 = (den_M082 : R)*monVal x mon_M082 := by
  exact monomial_gate x matrix_c matrix_cDen step081Left step081Right den_M052 den_M082 (x 3) vec_M052 vec_M082 mon_M052 mon_M082 (variableMon 3) step081_nonzero step081_scale step081_vector (matrix_c_columns x hWA) (monomial_M052 x hWA) step081_monomial (variableMon_value_3 x)
theorem monomial_M083 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M083 = (den_M083 : R)*monVal x mon_M083 := by
  exact monomial_gate x matrix_k matrix_kDen step082Left step082Right den_M049 den_M083 (x 2) vec_M049 vec_M083 mon_M049 mon_M083 (variableMon 2) step082_nonzero step082_scale step082_vector (matrix_k_columns x hWA) (monomial_M049 x hWA) step082_monomial (variableMon_value_2 x)
theorem monomial_M084 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M084 = (den_M084 : R)*monVal x mon_M084 := by
  exact monomial_gate x matrix_k matrix_kDen step083Left step083Right den_M050 den_M084 (x 2) vec_M050 vec_M084 mon_M050 mon_M084 (variableMon 2) step083_nonzero step083_scale step083_vector (matrix_k_columns x hWA) (monomial_M050 x hWA) step083_monomial (variableMon_value_2 x)
theorem monomial_M085 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M085 = (den_M085 : R)*monVal x mon_M085 := by
  exact monomial_gate x matrix_k matrix_kDen step084Left step084Right den_M051 den_M085 (x 2) vec_M051 vec_M085 mon_M051 mon_M085 (variableMon 2) step084_nonzero step084_scale step084_vector (matrix_k_columns x hWA) (monomial_M051 x hWA) step084_monomial (variableMon_value_2 x)
theorem monomial_M086 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M086 = (den_M086 : R)*monVal x mon_M086 := by
  exact monomial_gate x matrix_k matrix_kDen step085Left step085Right den_M053 den_M086 (x 2) vec_M053 vec_M086 mon_M053 mon_M086 (variableMon 2) step085_nonzero step085_scale step085_vector (matrix_k_columns x hWA) (monomial_M053 x hWA) step085_monomial (variableMon_value_2 x)
theorem monomial_M087 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M087 = (den_M087 : R)*monVal x mon_M087 := by
  exact monomial_gate x matrix_k matrix_kDen step086Left step086Right den_M054 den_M087 (x 2) vec_M054 vec_M087 mon_M054 mon_M087 (variableMon 2) step086_nonzero step086_scale step086_vector (matrix_k_columns x hWA) (monomial_M054 x hWA) step086_monomial (variableMon_value_2 x)
theorem monomial_M088 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M088 = (den_M088 : R)*monVal x mon_M088 := by
  exact monomial_gate x matrix_k matrix_kDen step087Left step087Right den_M055 den_M088 (x 2) vec_M055 vec_M088 mon_M055 mon_M088 (variableMon 2) step087_nonzero step087_scale step087_vector (matrix_k_columns x hWA) (monomial_M055 x hWA) step087_monomial (variableMon_value_2 x)
end N6.Weighted49
