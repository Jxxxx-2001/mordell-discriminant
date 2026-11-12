import N6.Weighted49.DInitialization
import N6.Weighted49.GateTransfer008
import N6.Weighted49.GateTransfer009
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem krylov_K001 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K001 = (den_K001 : R)*(value x N6.Dcolon1.dData * x 4 ^ 1) := by
  have hs : W (fun i => value x (basisData i)) vec_K000 = (den_K000 : R)*(value x N6.Dcolon1.dData * x 4 ^ 0) := by simpa using D_initialization x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step140Left step140Right den_K000 den_K001 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 0) vec_K000 vec_K001 step140_nonzero step140_scale step140_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 1 = x 4 ^ 0 * x 4 := pow_succ (x 4) 0
  rw [h, hp]
  ring
theorem krylov_K002 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K002 = (den_K002 : R)*(value x N6.Dcolon1.dData * x 4 ^ 2) := by
  have hs : W (fun i => value x (basisData i)) vec_K001 = (den_K001 : R)*(value x N6.Dcolon1.dData * x 4 ^ 1) := by simpa using krylov_K001 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step141Left step141Right den_K001 den_K002 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 1) vec_K001 vec_K002 step141_nonzero step141_scale step141_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 2 = x 4 ^ 1 * x 4 := pow_succ (x 4) 1
  rw [h, hp]
  ring
theorem krylov_K003 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K003 = (den_K003 : R)*(value x N6.Dcolon1.dData * x 4 ^ 3) := by
  have hs : W (fun i => value x (basisData i)) vec_K002 = (den_K002 : R)*(value x N6.Dcolon1.dData * x 4 ^ 2) := by simpa using krylov_K002 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step142Left step142Right den_K002 den_K003 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 2) vec_K002 vec_K003 step142_nonzero step142_scale step142_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 3 = x 4 ^ 2 * x 4 := pow_succ (x 4) 2
  rw [h, hp]
  ring
theorem krylov_K004 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K004 = (den_K004 : R)*(value x N6.Dcolon1.dData * x 4 ^ 4) := by
  have hs : W (fun i => value x (basisData i)) vec_K003 = (den_K003 : R)*(value x N6.Dcolon1.dData * x 4 ^ 3) := by simpa using krylov_K003 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step143Left step143Right den_K003 den_K004 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 3) vec_K003 vec_K004 step143_nonzero step143_scale step143_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 4 = x 4 ^ 3 * x 4 := pow_succ (x 4) 3
  rw [h, hp]
  ring
theorem krylov_K005 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K005 = (den_K005 : R)*(value x N6.Dcolon1.dData * x 4 ^ 5) := by
  have hs : W (fun i => value x (basisData i)) vec_K004 = (den_K004 : R)*(value x N6.Dcolon1.dData * x 4 ^ 4) := by simpa using krylov_K004 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step144Left step144Right den_K004 den_K005 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 4) vec_K004 vec_K005 step144_nonzero step144_scale step144_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 5 = x 4 ^ 4 * x 4 := pow_succ (x 4) 4
  rw [h, hp]
  ring
theorem krylov_K006 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K006 = (den_K006 : R)*(value x N6.Dcolon1.dData * x 4 ^ 6) := by
  have hs : W (fun i => value x (basisData i)) vec_K005 = (den_K005 : R)*(value x N6.Dcolon1.dData * x 4 ^ 5) := by simpa using krylov_K005 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step145Left step145Right den_K005 den_K006 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 5) vec_K005 vec_K006 step145_nonzero step145_scale step145_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 6 = x 4 ^ 5 * x 4 := pow_succ (x 4) 5
  rw [h, hp]
  ring
theorem krylov_K007 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K007 = (den_K007 : R)*(value x N6.Dcolon1.dData * x 4 ^ 7) := by
  have hs : W (fun i => value x (basisData i)) vec_K006 = (den_K006 : R)*(value x N6.Dcolon1.dData * x 4 ^ 6) := by simpa using krylov_K006 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step146Left step146Right den_K006 den_K007 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 6) vec_K006 vec_K007 step146_nonzero step146_scale step146_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 7 = x 4 ^ 6 * x 4 := pow_succ (x 4) 6
  rw [h, hp]
  ring
theorem krylov_K008 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K008 = (den_K008 : R)*(value x N6.Dcolon1.dData * x 4 ^ 8) := by
  have hs : W (fun i => value x (basisData i)) vec_K007 = (den_K007 : R)*(value x N6.Dcolon1.dData * x 4 ^ 7) := by simpa using krylov_K007 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step147Left step147Right den_K007 den_K008 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 7) vec_K007 vec_K008 step147_nonzero step147_scale step147_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 8 = x 4 ^ 7 * x 4 := pow_succ (x 4) 7
  rw [h, hp]
  ring
end N6.Weighted49
