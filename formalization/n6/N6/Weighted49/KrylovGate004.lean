import N6.Weighted49.KrylovGate003
import N6.Weighted49.GateTransfer010
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem krylov_K033 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K033 = (den_K033 : R)*(value x N6.Dcolon1.dData * x 4 ^ 33) := by
  have hs : W (fun i => value x (basisData i)) vec_K032 = (den_K032 : R)*(value x N6.Dcolon1.dData * x 4 ^ 32) := by simpa using krylov_K032 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step172Left step172Right den_K032 den_K033 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 32) vec_K032 vec_K033 step172_nonzero step172_scale step172_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 33 = x 4 ^ 32 * x 4 := pow_succ (x 4) 32
  rw [h, hp]
  ring
theorem krylov_K034 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K034 = (den_K034 : R)*(value x N6.Dcolon1.dData * x 4 ^ 34) := by
  have hs : W (fun i => value x (basisData i)) vec_K033 = (den_K033 : R)*(value x N6.Dcolon1.dData * x 4 ^ 33) := by simpa using krylov_K033 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step173Left step173Right den_K033 den_K034 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 33) vec_K033 vec_K034 step173_nonzero step173_scale step173_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 34 = x 4 ^ 33 * x 4 := pow_succ (x 4) 33
  rw [h, hp]
  ring
theorem krylov_K035 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K035 = (den_K035 : R)*(value x N6.Dcolon1.dData * x 4 ^ 35) := by
  have hs : W (fun i => value x (basisData i)) vec_K034 = (den_K034 : R)*(value x N6.Dcolon1.dData * x 4 ^ 34) := by simpa using krylov_K034 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step174Left step174Right den_K034 den_K035 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 34) vec_K034 vec_K035 step174_nonzero step174_scale step174_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 35 = x 4 ^ 34 * x 4 := pow_succ (x 4) 34
  rw [h, hp]
  ring
end N6.Weighted49
