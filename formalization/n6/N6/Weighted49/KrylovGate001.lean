import N6.Weighted49.KrylovGate000
import N6.Weighted49.GateTransfer009
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem krylov_K009 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K009 = (den_K009 : R)*(value x N6.Dcolon1.dData * x 4 ^ 9) := by
  have hs : W (fun i => value x (basisData i)) vec_K008 = (den_K008 : R)*(value x N6.Dcolon1.dData * x 4 ^ 8) := by simpa using krylov_K008 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step148Left step148Right den_K008 den_K009 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 8) vec_K008 vec_K009 step148_nonzero step148_scale step148_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 9 = x 4 ^ 8 * x 4 := pow_succ (x 4) 8
  rw [h, hp]
  ring
theorem krylov_K010 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K010 = (den_K010 : R)*(value x N6.Dcolon1.dData * x 4 ^ 10) := by
  have hs : W (fun i => value x (basisData i)) vec_K009 = (den_K009 : R)*(value x N6.Dcolon1.dData * x 4 ^ 9) := by simpa using krylov_K009 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step149Left step149Right den_K009 den_K010 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 9) vec_K009 vec_K010 step149_nonzero step149_scale step149_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 10 = x 4 ^ 9 * x 4 := pow_succ (x 4) 9
  rw [h, hp]
  ring
theorem krylov_K011 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K011 = (den_K011 : R)*(value x N6.Dcolon1.dData * x 4 ^ 11) := by
  have hs : W (fun i => value x (basisData i)) vec_K010 = (den_K010 : R)*(value x N6.Dcolon1.dData * x 4 ^ 10) := by simpa using krylov_K010 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step150Left step150Right den_K010 den_K011 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 10) vec_K010 vec_K011 step150_nonzero step150_scale step150_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 11 = x 4 ^ 10 * x 4 := pow_succ (x 4) 10
  rw [h, hp]
  ring
theorem krylov_K012 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K012 = (den_K012 : R)*(value x N6.Dcolon1.dData * x 4 ^ 12) := by
  have hs : W (fun i => value x (basisData i)) vec_K011 = (den_K011 : R)*(value x N6.Dcolon1.dData * x 4 ^ 11) := by simpa using krylov_K011 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step151Left step151Right den_K011 den_K012 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 11) vec_K011 vec_K012 step151_nonzero step151_scale step151_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 12 = x 4 ^ 11 * x 4 := pow_succ (x 4) 11
  rw [h, hp]
  ring
theorem krylov_K013 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K013 = (den_K013 : R)*(value x N6.Dcolon1.dData * x 4 ^ 13) := by
  have hs : W (fun i => value x (basisData i)) vec_K012 = (den_K012 : R)*(value x N6.Dcolon1.dData * x 4 ^ 12) := by simpa using krylov_K012 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step152Left step152Right den_K012 den_K013 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 12) vec_K012 vec_K013 step152_nonzero step152_scale step152_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 13 = x 4 ^ 12 * x 4 := pow_succ (x 4) 12
  rw [h, hp]
  ring
theorem krylov_K014 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K014 = (den_K014 : R)*(value x N6.Dcolon1.dData * x 4 ^ 14) := by
  have hs : W (fun i => value x (basisData i)) vec_K013 = (den_K013 : R)*(value x N6.Dcolon1.dData * x 4 ^ 13) := by simpa using krylov_K013 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step153Left step153Right den_K013 den_K014 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 13) vec_K013 vec_K014 step153_nonzero step153_scale step153_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 14 = x 4 ^ 13 * x 4 := pow_succ (x 4) 13
  rw [h, hp]
  ring
theorem krylov_K015 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K015 = (den_K015 : R)*(value x N6.Dcolon1.dData * x 4 ^ 15) := by
  have hs : W (fun i => value x (basisData i)) vec_K014 = (den_K014 : R)*(value x N6.Dcolon1.dData * x 4 ^ 14) := by simpa using krylov_K014 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step154Left step154Right den_K014 den_K015 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 14) vec_K014 vec_K015 step154_nonzero step154_scale step154_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 15 = x 4 ^ 14 * x 4 := pow_succ (x 4) 14
  rw [h, hp]
  ring
theorem krylov_K016 {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    W (fun i => value x (basisData i)) vec_K016 = (den_K016 : R)*(value x N6.Dcolon1.dData * x 4 ^ 16) := by
  have hs : W (fun i => value x (basisData i)) vec_K015 = (den_K015 : R)*(value x N6.Dcolon1.dData * x 4 ^ 15) := by simpa using krylov_K015 x hWA
  have h := action_gate (fun i => value x (basisData i)) matrix_B matrix_BDen step155Left step155Right den_K015 den_K016 (x 4) (value x N6.Dcolon1.dData * x 4 ^ 15) vec_K015 vec_K016 step155_nonzero step155_scale step155_vector (matrix_B_columns x hWA) hs
  have hp : x 4 ^ 16 = x 4 ^ 15 * x 4 := pow_succ (x 4) 15
  rw [h, hp]
  ring
end N6.Weighted49
