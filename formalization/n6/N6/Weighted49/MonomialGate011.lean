import N6.Weighted49.MonomialGate010
import N6.Weighted49.GateTransfer005
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M089 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M089 = (den_M089 : R)*monVal x mon_M089 := by
  exact monomial_gate x matrix_k matrix_kDen step088Left step088Right den_M056 den_M089 (x 2) vec_M056 vec_M089 mon_M056 mon_M089 (variableMon 2) step088_nonzero step088_scale step088_vector (matrix_k_columns x hWA) (monomial_M056 x hWA) step088_monomial (variableMon_value_2 x)
theorem monomial_M090 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M090 = (den_M090 : R)*monVal x mon_M090 := by
  exact monomial_gate x matrix_k matrix_kDen step089Left step089Right den_M057 den_M090 (x 2) vec_M057 vec_M090 mon_M057 mon_M090 (variableMon 2) step089_nonzero step089_scale step089_vector (matrix_k_columns x hWA) (monomial_M057 x hWA) step089_monomial (variableMon_value_2 x)
theorem monomial_M091 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M091 = (den_M091 : R)*monVal x mon_M091 := by
  exact monomial_gate x matrix_k matrix_kDen step090Left step090Right den_M058 den_M091 (x 2) vec_M058 vec_M091 mon_M058 mon_M091 (variableMon 2) step090_nonzero step090_scale step090_vector (matrix_k_columns x hWA) (monomial_M058 x hWA) step090_monomial (variableMon_value_2 x)
theorem monomial_M092 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M092 = (den_M092 : R)*monVal x mon_M092 := by
  exact monomial_gate x matrix_k matrix_kDen step091Left step091Right den_M060 den_M092 (x 2) vec_M060 vec_M092 mon_M060 mon_M092 (variableMon 2) step091_nonzero step091_scale step091_vector (matrix_k_columns x hWA) (monomial_M060 x hWA) step091_monomial (variableMon_value_2 x)
theorem monomial_M093 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M093 = (den_M093 : R)*monVal x mon_M093 := by
  exact monomial_gate x matrix_e matrix_eDen step092Left step092Right den_M050 den_M093 (x 1) vec_M050 vec_M093 mon_M050 mon_M093 (variableMon 1) step092_nonzero step092_scale step092_vector (matrix_e_columns x hWA) (monomial_M050 x hWA) step092_monomial (variableMon_value_1 x)
theorem monomial_M094 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M094 = (den_M094 : R)*monVal x mon_M094 := by
  exact monomial_gate x matrix_e matrix_eDen step093Left step093Right den_M051 den_M094 (x 1) vec_M051 vec_M094 mon_M051 mon_M094 (variableMon 1) step093_nonzero step093_scale step093_vector (matrix_e_columns x hWA) (monomial_M051 x hWA) step093_monomial (variableMon_value_1 x)
theorem monomial_M095 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M095 = (den_M095 : R)*monVal x mon_M095 := by
  exact monomial_gate x matrix_e matrix_eDen step094Left step094Right den_M052 den_M095 (x 1) vec_M052 vec_M095 mon_M052 mon_M095 (variableMon 1) step094_nonzero step094_scale step094_vector (matrix_e_columns x hWA) (monomial_M052 x hWA) step094_monomial (variableMon_value_1 x)
theorem monomial_M096 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M096 = (den_M096 : R)*monVal x mon_M096 := by
  exact monomial_gate x matrix_e matrix_eDen step095Left step095Right den_M054 den_M096 (x 1) vec_M054 vec_M096 mon_M054 mon_M096 (variableMon 1) step095_nonzero step095_scale step095_vector (matrix_e_columns x hWA) (monomial_M054 x hWA) step095_monomial (variableMon_value_1 x)
end N6.Weighted49
