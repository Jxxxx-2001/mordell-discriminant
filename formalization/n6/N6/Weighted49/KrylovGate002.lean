import N6.Weighted49.KrylovGate001
import N6.Weighted49.GateTransfer009
import N6.Weighted49.GateTransfer010
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem krylov_K017 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K017 = (den_K017 : R)*(value x N6.Dcolon1.dData * x 4 ^ 17) := by
  have hs : W (fun i => value x (basisData i)) vec_K016 = (den_K016 : R)*(value x N6.Dcolon1.dData * x 4 ^ 16) := by simpa using krylov_K016 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step156Left step156Right den_K016 den_K017 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 16) vec_K016 vec_K017 step156_nonzero step156_scale step156_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 17 = x 4 ^ 16 * x 4 := pow_succ (x 4) 16
  rw [h, hp]
  ring
theorem krylov_K018 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K018 = (den_K018 : R)*(value x N6.Dcolon1.dData * x 4 ^ 18) := by
  have hs : W (fun i => value x (basisData i)) vec_K017 = (den_K017 : R)*(value x N6.Dcolon1.dData * x 4 ^ 17) := by simpa using krylov_K017 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step157Left step157Right den_K017 den_K018 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 17) vec_K017 vec_K018 step157_nonzero step157_scale step157_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 18 = x 4 ^ 17 * x 4 := pow_succ (x 4) 17
  rw [h, hp]
  ring
theorem krylov_K019 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K019 = (den_K019 : R)*(value x N6.Dcolon1.dData * x 4 ^ 19) := by
  have hs : W (fun i => value x (basisData i)) vec_K018 = (den_K018 : R)*(value x N6.Dcolon1.dData * x 4 ^ 18) := by simpa using krylov_K018 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step158Left step158Right den_K018 den_K019 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 18) vec_K018 vec_K019 step158_nonzero step158_scale step158_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 19 = x 4 ^ 18 * x 4 := pow_succ (x 4) 18
  rw [h, hp]
  ring
theorem krylov_K020 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K020 = (den_K020 : R)*(value x N6.Dcolon1.dData * x 4 ^ 20) := by
  have hs : W (fun i => value x (basisData i)) vec_K019 = (den_K019 : R)*(value x N6.Dcolon1.dData * x 4 ^ 19) := by simpa using krylov_K019 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step159Left step159Right den_K019 den_K020 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 19) vec_K019 vec_K020 step159_nonzero step159_scale step159_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 20 = x 4 ^ 19 * x 4 := pow_succ (x 4) 19
  rw [h, hp]
  ring
theorem krylov_K021 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K021 = (den_K021 : R)*(value x N6.Dcolon1.dData * x 4 ^ 21) := by
  have hs : W (fun i => value x (basisData i)) vec_K020 = (den_K020 : R)*(value x N6.Dcolon1.dData * x 4 ^ 20) := by simpa using krylov_K020 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step160Left step160Right den_K020 den_K021 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 20) vec_K020 vec_K021 step160_nonzero step160_scale step160_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 21 = x 4 ^ 20 * x 4 := pow_succ (x 4) 20
  rw [h, hp]
  ring
theorem krylov_K022 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K022 = (den_K022 : R)*(value x N6.Dcolon1.dData * x 4 ^ 22) := by
  have hs : W (fun i => value x (basisData i)) vec_K021 = (den_K021 : R)*(value x N6.Dcolon1.dData * x 4 ^ 21) := by simpa using krylov_K021 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step161Left step161Right den_K021 den_K022 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 21) vec_K021 vec_K022 step161_nonzero step161_scale step161_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 22 = x 4 ^ 21 * x 4 := pow_succ (x 4) 21
  rw [h, hp]
  ring
theorem krylov_K023 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K023 = (den_K023 : R)*(value x N6.Dcolon1.dData * x 4 ^ 23) := by
  have hs : W (fun i => value x (basisData i)) vec_K022 = (den_K022 : R)*(value x N6.Dcolon1.dData * x 4 ^ 22) := by simpa using krylov_K022 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step162Left step162Right den_K022 den_K023 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 22) vec_K022 vec_K023 step162_nonzero step162_scale step162_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 23 = x 4 ^ 22 * x 4 := pow_succ (x 4) 22
  rw [h, hp]
  ring
theorem krylov_K024 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K024 = (den_K024 : R)*(value x N6.Dcolon1.dData * x 4 ^ 24) := by
  have hs : W (fun i => value x (basisData i)) vec_K023 = (den_K023 : R)*(value x N6.Dcolon1.dData * x 4 ^ 23) := by simpa using krylov_K023 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step163Left step163Right den_K023 den_K024 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 23) vec_K023 vec_K024 step163_nonzero step163_scale step163_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 24 = x 4 ^ 23 * x 4 := pow_succ (x 4) 23
  rw [h, hp]
  ring
end N6.Weighted49
