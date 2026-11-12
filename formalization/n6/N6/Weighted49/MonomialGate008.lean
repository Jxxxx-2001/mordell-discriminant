import N6.Weighted49.MonomialGate007
import N6.Weighted49.GateTransfer004
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M065 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M065 = (den_M065 : R)*monVal x mon_M065 := by
  exact monomial_gate x matrix_e matrix_eDen step064Left step064Right den_M033 den_M065 (x 1) vec_M033 vec_M065 mon_M033 mon_M065 (variableMon 1) step064_nonzero step064_scale step064_vector (matrix_e_columns x hWA) (monomial_M033 x hWA) step064_monomial (variableMon_value_1 x)
theorem monomial_M066 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M066 = (den_M066 : R)*monVal x mon_M066 := by
  exact monomial_gate x matrix_e matrix_eDen step065Left step065Right den_M034 den_M066 (x 1) vec_M034 vec_M066 mon_M034 mon_M066 (variableMon 1) step065_nonzero step065_scale step065_vector (matrix_e_columns x hWA) (monomial_M034 x hWA) step065_monomial (variableMon_value_1 x)
theorem monomial_M067 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M067 = (den_M067 : R)*monVal x mon_M067 := by
  exact monomial_gate x matrix_e matrix_eDen step066Left step066Right den_M035 den_M067 (x 1) vec_M035 vec_M067 mon_M035 mon_M067 (variableMon 1) step066_nonzero step066_scale step066_vector (matrix_e_columns x hWA) (monomial_M035 x hWA) step066_monomial (variableMon_value_1 x)
theorem monomial_M068 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M068 = (den_M068 : R)*monVal x mon_M068 := by
  exact monomial_gate x matrix_e matrix_eDen step067Left step067Right den_M036 den_M068 (x 1) vec_M036 vec_M068 mon_M036 mon_M068 (variableMon 1) step067_nonzero step067_scale step067_vector (matrix_e_columns x hWA) (monomial_M036 x hWA) step067_monomial (variableMon_value_1 x)
theorem monomial_M069 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M069 = (den_M069 : R)*monVal x mon_M069 := by
  exact monomial_gate x matrix_e matrix_eDen step068Left step068Right den_M037 den_M069 (x 1) vec_M037 vec_M069 mon_M037 mon_M069 (variableMon 1) step068_nonzero step068_scale step068_vector (matrix_e_columns x hWA) (monomial_M037 x hWA) step068_monomial (variableMon_value_1 x)
theorem monomial_M070 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M070 = (den_M070 : R)*monVal x mon_M070 := by
  exact monomial_gate x matrix_e matrix_eDen step069Left step069Right den_M038 den_M070 (x 1) vec_M038 vec_M070 mon_M038 mon_M070 (variableMon 1) step069_nonzero step069_scale step069_vector (matrix_e_columns x hWA) (monomial_M038 x hWA) step069_monomial (variableMon_value_1 x)
theorem monomial_M071 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M071 = (den_M071 : R)*monVal x mon_M071 := by
  exact monomial_gate x matrix_e matrix_eDen step070Left step070Right den_M039 den_M071 (x 1) vec_M039 vec_M071 mon_M039 mon_M071 (variableMon 1) step070_nonzero step070_scale step070_vector (matrix_e_columns x hWA) (monomial_M039 x hWA) step070_monomial (variableMon_value_1 x)
theorem monomial_M072 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M072 = (den_M072 : R)*monVal x mon_M072 := by
  exact monomial_gate x matrix_e matrix_eDen step071Left step071Right den_M040 den_M072 (x 1) vec_M040 vec_M072 mon_M040 mon_M072 (variableMon 1) step071_nonzero step071_scale step071_vector (matrix_e_columns x hWA) (monomial_M040 x hWA) step071_monomial (variableMon_value_1 x)
end N6.Weighted49
