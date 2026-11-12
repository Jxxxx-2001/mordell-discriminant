import N6.Weighted49.DInitialization
import N6.Weighted49.GateTransfer008
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem weighted_c {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_D_c = (den_D_c : R)*(value x N6.Dcolon1.dData*x 3) := by
  have h := action_gate (fun i => value x (basisData i)) matrix_c matrix_cDen step137Left step137Right den_K000 den_D_c (x 3) (value x N6.Dcolon1.dData) vec_K000 vec_D_c step137_nonzero step137_scale step137_vector (matrix_c_columns x hWA) (D_initialization x hWA)
  rw [h]
  ring
theorem weighted_k {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_D_k = (den_D_k : R)*(value x N6.Dcolon1.dData*x 2) := by
  have h := action_gate (fun i => value x (basisData i)) matrix_k matrix_kDen step138Left step138Right den_K000 den_D_k (x 2) (value x N6.Dcolon1.dData) vec_K000 vec_D_k step138_nonzero step138_scale step138_vector (matrix_k_columns x hWA) (D_initialization x hWA)
  rw [h]
  ring
theorem weighted_e {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_D_e = (den_D_e : R)*(value x N6.Dcolon1.dData*x 1) := by
  have h := action_gate (fun i => value x (basisData i)) matrix_e matrix_eDen step139Left step139Right den_K000 den_D_e (x 1) (value x N6.Dcolon1.dData) vec_K000 vec_D_e step139_nonzero step139_scale step139_vector (matrix_e_columns x hWA) (D_initialization x hWA)
  rw [h]
  ring
end N6.Weighted49
