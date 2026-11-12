import N6.Weighted49.MonomialGate000
import N6.Weighted49.GateTransfer000
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem monomial_M009 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M009 = (den_M009 : R)*monVal x mon_M009 := by
  exact monomial_gate x matrix_e matrix_eDen step008Left step008Right den_M002 den_M009 (x 1) vec_M002 vec_M009 mon_M002 mon_M009 (variableMon 1) step008_nonzero step008_scale step008_vector (matrix_e_columns x hWA) (monomial_M002 x hWA) step008_monomial (variableMon_value_1 x)
theorem monomial_M010 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M010 = (den_M010 : R)*monVal x mon_M010 := by
  exact monomial_gate x matrix_e matrix_eDen step009Left step009Right den_M003 den_M010 (x 1) vec_M003 vec_M010 mon_M003 mon_M010 (variableMon 1) step009_nonzero step009_scale step009_vector (matrix_e_columns x hWA) (monomial_M003 x hWA) step009_monomial (variableMon_value_1 x)
theorem monomial_M011 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M011 = (den_M011 : R)*monVal x mon_M011 := by
  exact monomial_gate x matrix_B matrix_BDen step010Left step010Right den_M004 den_M011 (x 4) vec_M004 vec_M011 mon_M004 mon_M011 (variableMon 4) step010_nonzero step010_scale step010_vector (matrix_B_columns x hWA) (monomial_M004 x hWA) step010_monomial (variableMon_value_4 x)
theorem monomial_M012 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M012 = (den_M012 : R)*monVal x mon_M012 := by
  exact monomial_gate x matrix_c matrix_cDen step011Left step011Right den_M004 den_M012 (x 3) vec_M004 vec_M012 mon_M004 mon_M012 (variableMon 3) step011_nonzero step011_scale step011_vector (matrix_c_columns x hWA) (monomial_M004 x hWA) step011_monomial (variableMon_value_3 x)
theorem monomial_M013 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M013 = (den_M013 : R)*monVal x mon_M013 := by
  exact monomial_gate x matrix_c matrix_cDen step012Left step012Right den_M005 den_M013 (x 3) vec_M005 vec_M013 mon_M005 mon_M013 (variableMon 3) step012_nonzero step012_scale step012_vector (matrix_c_columns x hWA) (monomial_M005 x hWA) step012_monomial (variableMon_value_3 x)
theorem monomial_M014 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M014 = (den_M014 : R)*monVal x mon_M014 := by
  exact monomial_gate x matrix_c matrix_cDen step013Left step013Right den_M006 den_M014 (x 3) vec_M006 vec_M014 mon_M006 mon_M014 (variableMon 3) step013_nonzero step013_scale step013_vector (matrix_c_columns x hWA) (monomial_M006 x hWA) step013_monomial (variableMon_value_3 x)
theorem monomial_M015 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M015 = (den_M015 : R)*monVal x mon_M015 := by
  exact monomial_gate x matrix_k matrix_kDen step014Left step014Right den_M004 den_M015 (x 2) vec_M004 vec_M015 mon_M004 mon_M015 (variableMon 2) step014_nonzero step014_scale step014_vector (matrix_k_columns x hWA) (monomial_M004 x hWA) step014_monomial (variableMon_value_2 x)
theorem monomial_M016 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_M016 = (den_M016 : R)*monVal x mon_M016 := by
  exact monomial_gate x matrix_k matrix_kDen step015Left step015Right den_M005 den_M016 (x 2) vec_M005 vec_M016 mon_M005 mon_M016 (variableMon 2) step015_nonzero step015_scale step015_vector (matrix_k_columns x hWA) (monomial_M005 x hWA) step015_monomial (variableMon_value_2 x)
end N6.Weighted49
