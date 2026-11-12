import N6.Weighted49.ColumnGround006
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column048_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column048Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column048Pairs column048Checked
  have hw : value x WA024 = 0 := by simpa only [actionData] using hWA 24
  simp only [column048Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column048Clearing column048Clearing_ne_zero _ h
theorem column048_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 48) = W (fun i => value x (basisData i)) (fun i => matrix_e i 48) := by
  have h := column048_value_zero x hWA
  rw [column048Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column048_identity
theorem column049_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column049Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column049Pairs column049Checked
  simp only [column049Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column049Clearing column049Clearing_ne_zero _ h
theorem column049_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 0) = W (fun i => value x (basisData i)) (fun i => matrix_k i 0) := by
  have h := column049_value_zero x hWA
  rw [column049Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column049_identity
theorem column050_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column050Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column050Pairs column050Checked
  simp only [column050Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column050Clearing column050Clearing_ne_zero _ h
theorem column050_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 1) = W (fun i => value x (basisData i)) (fun i => matrix_k i 1) := by
  have h := column050_value_zero x hWA
  rw [column050Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column050_identity
theorem column051_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column051Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column051Pairs column051Checked
  simp only [column051Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column051Clearing column051Clearing_ne_zero _ h
theorem column051_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 2) = W (fun i => value x (basisData i)) (fun i => matrix_k i 2) := by
  have h := column051_value_zero x hWA
  rw [column051Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column051_identity
theorem column052_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column052Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column052Pairs column052Checked
  simp only [column052Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column052Clearing column052Clearing_ne_zero _ h
theorem column052_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 3) = W (fun i => value x (basisData i)) (fun i => matrix_k i 3) := by
  have h := column052_value_zero x hWA
  rw [column052Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column052_identity
theorem column053_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column053Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column053Pairs column053Checked
  simp only [column053Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column053Clearing column053Clearing_ne_zero _ h
theorem column053_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 4) = W (fun i => value x (basisData i)) (fun i => matrix_k i 4) := by
  have h := column053_value_zero x hWA
  rw [column053Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column053_identity
theorem column054_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column054Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column054Pairs column054Checked
  simp only [column054Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column054Clearing column054Clearing_ne_zero _ h
theorem column054_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 5) = W (fun i => value x (basisData i)) (fun i => matrix_k i 5) := by
  have h := column054_value_zero x hWA
  rw [column054Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column054_identity
theorem column055_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column055Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column055Pairs column055Checked
  simp only [column055Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column055Clearing column055Clearing_ne_zero _ h
theorem column055_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 6) = W (fun i => value x (basisData i)) (fun i => matrix_k i 6) := by
  have h := column055_value_zero x hWA
  rw [column055Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column055_identity
end N6.Weighted49
