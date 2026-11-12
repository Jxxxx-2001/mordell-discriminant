import N6.Weighted49.ColumnGround007
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column056_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column056Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column056Pairs column056Checked
  simp only [column056Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column056Clearing column056Clearing_ne_zero _ h
theorem column056_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 7) = W (fun i => value x (basisData i)) (fun i => matrix_k i 7) := by
  have h := column056_value_zero x hWA
  rw [column056Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column056_identity
theorem column057_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column057Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column057Pairs column057Checked
  simp only [column057Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column057Clearing column057Clearing_ne_zero _ h
theorem column057_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 8) = W (fun i => value x (basisData i)) (fun i => matrix_k i 8) := by
  have h := column057_value_zero x hWA
  rw [column057Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column057_identity
theorem column058_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column058Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column058Pairs column058Checked
  simp only [column058Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column058Clearing column058Clearing_ne_zero _ h
theorem column058_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 9) = W (fun i => value x (basisData i)) (fun i => matrix_k i 9) := by
  have h := column058_value_zero x hWA
  rw [column058Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column058_identity
theorem column059_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column059Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column059Pairs column059Checked
  simp only [column059Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column059Clearing column059Clearing_ne_zero _ h
theorem column059_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 10) = W (fun i => value x (basisData i)) (fun i => matrix_k i 10) := by
  have h := column059_value_zero x hWA
  rw [column059Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column059_identity
theorem column060_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column060Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column060Pairs column060Checked
  simp only [column060Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column060Clearing column060Clearing_ne_zero _ h
theorem column060_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 11) = W (fun i => value x (basisData i)) (fun i => matrix_k i 11) := by
  have h := column060_value_zero x hWA
  rw [column060Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column060_identity
theorem column061_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column061Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column061Pairs column061Checked
  simp only [column061Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column061Clearing column061Clearing_ne_zero _ h
theorem column061_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 12) = W (fun i => value x (basisData i)) (fun i => matrix_k i 12) := by
  have h := column061_value_zero x hWA
  rw [column061Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column061_identity
theorem column062_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column062Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column062Pairs column062Checked
  simp only [column062Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column062Clearing column062Clearing_ne_zero _ h
theorem column062_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 13) = W (fun i => value x (basisData i)) (fun i => matrix_k i 13) := by
  have h := column062_value_zero x hWA
  rw [column062Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column062_identity
theorem column063_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column063Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column063Pairs column063Checked
  simp only [column063Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column063Clearing column063Clearing_ne_zero _ h
theorem column063_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 14) = W (fun i => value x (basisData i)) (fun i => matrix_k i 14) := by
  have h := column063_value_zero x hWA
  rw [column063Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column063_identity
end N6.Weighted49
