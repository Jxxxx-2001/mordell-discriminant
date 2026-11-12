import N6.Weighted49.KrylovGate002
import N6.Weighted49.GateTransfer010
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem krylov_K025 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K025 = (den_K025 : R)*(value x N6.Dcolon1.dData * x 4 ^ 25) := by
  have hs : W (fun i => value x (basisData i)) vec_K024 = (den_K024 : R)*(value x N6.Dcolon1.dData * x 4 ^ 24) := by simpa using krylov_K024 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step164Left step164Right den_K024 den_K025 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 24) vec_K024 vec_K025 step164_nonzero step164_scale step164_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 25 = x 4 ^ 24 * x 4 := pow_succ (x 4) 24
  rw [h, hp]
  ring
theorem krylov_K026 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K026 = (den_K026 : R)*(value x N6.Dcolon1.dData * x 4 ^ 26) := by
  have hs : W (fun i => value x (basisData i)) vec_K025 = (den_K025 : R)*(value x N6.Dcolon1.dData * x 4 ^ 25) := by simpa using krylov_K025 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step165Left step165Right den_K025 den_K026 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 25) vec_K025 vec_K026 step165_nonzero step165_scale step165_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 26 = x 4 ^ 25 * x 4 := pow_succ (x 4) 25
  rw [h, hp]
  ring
theorem krylov_K027 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K027 = (den_K027 : R)*(value x N6.Dcolon1.dData * x 4 ^ 27) := by
  have hs : W (fun i => value x (basisData i)) vec_K026 = (den_K026 : R)*(value x N6.Dcolon1.dData * x 4 ^ 26) := by simpa using krylov_K026 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step166Left step166Right den_K026 den_K027 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 26) vec_K026 vec_K027 step166_nonzero step166_scale step166_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 27 = x 4 ^ 26 * x 4 := pow_succ (x 4) 26
  rw [h, hp]
  ring
theorem krylov_K028 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K028 = (den_K028 : R)*(value x N6.Dcolon1.dData * x 4 ^ 28) := by
  have hs : W (fun i => value x (basisData i)) vec_K027 = (den_K027 : R)*(value x N6.Dcolon1.dData * x 4 ^ 27) := by simpa using krylov_K027 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step167Left step167Right den_K027 den_K028 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 27) vec_K027 vec_K028 step167_nonzero step167_scale step167_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 28 = x 4 ^ 27 * x 4 := pow_succ (x 4) 27
  rw [h, hp]
  ring
theorem krylov_K029 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K029 = (den_K029 : R)*(value x N6.Dcolon1.dData * x 4 ^ 29) := by
  have hs : W (fun i => value x (basisData i)) vec_K028 = (den_K028 : R)*(value x N6.Dcolon1.dData * x 4 ^ 28) := by simpa using krylov_K028 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step168Left step168Right den_K028 den_K029 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 28) vec_K028 vec_K029 step168_nonzero step168_scale step168_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 29 = x 4 ^ 28 * x 4 := pow_succ (x 4) 28
  rw [h, hp]
  ring
theorem krylov_K030 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K030 = (den_K030 : R)*(value x N6.Dcolon1.dData * x 4 ^ 30) := by
  have hs : W (fun i => value x (basisData i)) vec_K029 = (den_K029 : R)*(value x N6.Dcolon1.dData * x 4 ^ 29) := by simpa using krylov_K029 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step169Left step169Right den_K029 den_K030 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 29) vec_K029 vec_K030 step169_nonzero step169_scale step169_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 30 = x 4 ^ 29 * x 4 := pow_succ (x 4) 29
  rw [h, hp]
  ring
theorem krylov_K031 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K031 = (den_K031 : R)*(value x N6.Dcolon1.dData * x 4 ^ 31) := by
  have hs : W (fun i => value x (basisData i)) vec_K030 = (den_K030 : R)*(value x N6.Dcolon1.dData * x 4 ^ 30) := by simpa using krylov_K030 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step170Left step170Right den_K030 den_K031 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 30) vec_K030 vec_K031 step170_nonzero step170_scale step170_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 31 = x 4 ^ 30 * x 4 := pow_succ (x 4) 30
  rw [h, hp]
  ring
theorem krylov_K032 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K032 = (den_K032 : R)*(value x N6.Dcolon1.dData * x 4 ^ 32) := by
  have hs : W (fun i => value x (basisData i)) vec_K031 = (den_K031 : R)*(value x N6.Dcolon1.dData * x 4 ^ 31) := by simpa using krylov_K031 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step171Left step171Right den_K031 den_K032 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 31) vec_K031 vec_K032 step171_nonzero step171_scale step171_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 32 = x 4 ^ 31 * x 4 := pow_succ (x 4) 31
  rw [h, hp]
  ring
end N6.Weighted49
