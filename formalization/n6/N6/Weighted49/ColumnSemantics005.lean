import N6.Weighted49.ColumnGround005
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column040_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column040Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column040Pairs column040Checked
  have hw : value x WA048 = 0 := by simpa only [actionData] using hWA 48
  simp only [column040Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column040Clearing column040Clearing_ne_zero _ h
theorem column040_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 40) = W (fun i => value x (basisData i)) (fun i => matrix_e i 40) := by
  have h := column040_value_zero x hWA
  rw [column040Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column040_identity
theorem column041_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column041Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column041Pairs column041Checked
  have hw : value x WA038 = 0 := by simpa only [actionData] using hWA 38
  simp only [column041Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column041Clearing column041Clearing_ne_zero _ h
theorem column041_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 41) = W (fun i => value x (basisData i)) (fun i => matrix_e i 41) := by
  have h := column041_value_zero x hWA
  rw [column041Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column041_identity
theorem column042_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column042Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column042Pairs column042Checked
  have hw : value x WA045 = 0 := by simpa only [actionData] using hWA 45
  simp only [column042Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column042Clearing column042Clearing_ne_zero _ h
theorem column042_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 42) = W (fun i => value x (basisData i)) (fun i => matrix_e i 42) := by
  have h := column042_value_zero x hWA
  rw [column042Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column042_identity
theorem column043_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column043Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column043Pairs column043Checked
  have hw : value x WA035 = 0 := by simpa only [actionData] using hWA 35
  simp only [column043Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column043Clearing column043Clearing_ne_zero _ h
theorem column043_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 43) = W (fun i => value x (basisData i)) (fun i => matrix_e i 43) := by
  have h := column043_value_zero x hWA
  rw [column043Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column043_identity
theorem column044_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column044Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column044Pairs column044Checked
  have hw : value x WA029 = 0 := by simpa only [actionData] using hWA 29
  simp only [column044Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column044Clearing column044Clearing_ne_zero _ h
theorem column044_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 44) = W (fun i => value x (basisData i)) (fun i => matrix_e i 44) := by
  have h := column044_value_zero x hWA
  rw [column044Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column044_identity
theorem column045_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column045Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column045Pairs column045Checked
  have hw : value x WA043 = 0 := by simpa only [actionData] using hWA 43
  simp only [column045Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column045Clearing column045Clearing_ne_zero _ h
theorem column045_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 45) = W (fun i => value x (basisData i)) (fun i => matrix_e i 45) := by
  have h := column045_value_zero x hWA
  rw [column045Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column045_identity
theorem column046_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column046Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column046Pairs column046Checked
  have hw : value x WA033 = 0 := by simpa only [actionData] using hWA 33
  simp only [column046Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column046Clearing column046Clearing_ne_zero _ h
theorem column046_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 46) = W (fun i => value x (basisData i)) (fun i => matrix_e i 46) := by
  have h := column046_value_zero x hWA
  rw [column046Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column046_identity
theorem column047_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column047Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column047Pairs column047Checked
  have hw : value x WA027 = 0 := by simpa only [actionData] using hWA 27
  simp only [column047Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column047Clearing column047Clearing_ne_zero _ h
theorem column047_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 47) = W (fun i => value x (basisData i)) (fun i => matrix_e i 47) := by
  have h := column047_value_zero x hWA
  rw [column047Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column047_identity
end N6.Weighted49
