import N6.Weighted49.ColumnGround009
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column072_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column072Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column072Pairs column072Checked
  have hw : value x WA000 = 0 := by simpa only [actionData] using hWA 0
  simp only [column072Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column072Clearing column072Clearing_ne_zero _ h
theorem column072_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 23) = W (fun i => value x (basisData i)) (fun i => matrix_k i 23) := by
  have h := column072_value_zero x hWA
  rw [column072Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column072_identity
theorem column073_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column073Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column073Pairs column073Checked
  simp only [column073Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column073Clearing column073Clearing_ne_zero _ h
theorem column073_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 24) = W (fun i => value x (basisData i)) (fun i => matrix_k i 24) := by
  have h := column073_value_zero x hWA
  rw [column073Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column073_identity
theorem column074_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column074Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column074Pairs column074Checked
  have hw : value x WA016 = 0 := by simpa only [actionData] using hWA 16
  simp only [column074Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column074Clearing column074Clearing_ne_zero _ h
theorem column074_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 25) = W (fun i => value x (basisData i)) (fun i => matrix_k i 25) := by
  have h := column074_value_zero x hWA
  rw [column074Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column074_identity
theorem column075_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column075Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column075Pairs column075Checked
  have hw : value x WA012 = 0 := by simpa only [actionData] using hWA 12
  simp only [column075Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column075Clearing column075Clearing_ne_zero _ h
theorem column075_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 26) = W (fun i => value x (basisData i)) (fun i => matrix_k i 26) := by
  have h := column075_value_zero x hWA
  rw [column075Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column075_identity
theorem column076_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column076Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column076Pairs column076Checked
  have hw : value x WA002 = 0 := by simpa only [actionData] using hWA 2
  simp only [column076Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column076Clearing column076Clearing_ne_zero _ h
theorem column076_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 27) = W (fun i => value x (basisData i)) (fun i => matrix_k i 27) := by
  have h := column076_value_zero x hWA
  rw [column076Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column076_identity
theorem column077_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column077Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column077Pairs column077Checked
  have hw : value x WA009 = 0 := by simpa only [actionData] using hWA 9
  simp only [column077Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column077Clearing column077Clearing_ne_zero _ h
theorem column077_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 28) = W (fun i => value x (basisData i)) (fun i => matrix_k i 28) := by
  have h := column077_value_zero x hWA
  rw [column077Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column077_identity
theorem column078_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column078Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column078Pairs column078Checked
  simp only [column078Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column078Clearing column078Clearing_ne_zero _ h
theorem column078_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 29) = W (fun i => value x (basisData i)) (fun i => matrix_k i 29) := by
  have h := column078_value_zero x hWA
  rw [column078Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column078_identity
theorem column079_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column079Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column079Pairs column079Checked
  simp only [column079Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column079Clearing column079Clearing_ne_zero _ h
theorem column079_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 30) = W (fun i => value x (basisData i)) (fun i => matrix_k i 30) := by
  have h := column079_value_zero x hWA
  rw [column079Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column079_identity
end N6.Weighted49
