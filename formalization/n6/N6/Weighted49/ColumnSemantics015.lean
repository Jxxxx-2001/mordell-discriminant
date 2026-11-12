import N6.Weighted49.ColumnGround015
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column120_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column120Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column120Pairs column120Checked
  have hw : value x WA008 = 0 := by simpa only [actionData] using hWA 8
  simp only [column120Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column120Clearing column120Clearing_ne_zero _ h
theorem column120_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 22) = W (fun i => value x (basisData i)) (fun i => matrix_c i 22) := by
  have h := column120_value_zero x hWA
  rw [column120Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column120_identity
theorem column121_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column121Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column121Pairs column121Checked
  simp only [column121Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column121Clearing column121Clearing_ne_zero _ h
theorem column121_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 23) = W (fun i => value x (basisData i)) (fun i => matrix_c i 23) := by
  have h := column121_value_zero x hWA
  rw [column121Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column121_identity
theorem column122_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column122Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column122Pairs column122Checked
  simp only [column122Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column122Clearing column122Clearing_ne_zero _ h
theorem column122_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 24) = W (fun i => value x (basisData i)) (fun i => matrix_c i 24) := by
  have h := column122_value_zero x hWA
  rw [column122Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column122_identity
theorem column123_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column123Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column123Pairs column123Checked
  have hw : value x WA012 = 0 := by simpa only [actionData] using hWA 12
  simp only [column123Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column123Clearing column123Clearing_ne_zero _ h
theorem column123_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 25) = W (fun i => value x (basisData i)) (fun i => matrix_c i 25) := by
  have h := column123_value_zero x hWA
  rw [column123Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column123_identity
theorem column124_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column124Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column124Pairs column124Checked
  have hw : value x WA009 = 0 := by simpa only [actionData] using hWA 9
  simp only [column124Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column124Clearing column124Clearing_ne_zero _ h
theorem column124_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 26) = W (fun i => value x (basisData i)) (fun i => matrix_c i 26) := by
  have h := column124_value_zero x hWA
  rw [column124Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column124_identity
theorem column125_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column125Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column125Pairs column125Checked
  simp only [column125Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column125Clearing column125Clearing_ne_zero _ h
theorem column125_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 27) = W (fun i => value x (basisData i)) (fun i => matrix_c i 27) := by
  have h := column125_value_zero x hWA
  rw [column125Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column125_identity
theorem column126_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column126Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column126Pairs column126Checked
  have hw : value x WA007 = 0 := by simpa only [actionData] using hWA 7
  simp only [column126Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column126Clearing column126Clearing_ne_zero _ h
theorem column126_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 28) = W (fun i => value x (basisData i)) (fun i => matrix_c i 28) := by
  have h := column126_value_zero x hWA
  rw [column126Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column126_identity
theorem column127_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column127Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column127Pairs column127Checked
  simp only [column127Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column127Clearing column127Clearing_ne_zero _ h
theorem column127_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 29) = W (fun i => value x (basisData i)) (fun i => matrix_c i 29) := by
  have h := column127_value_zero x hWA
  rw [column127Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column127_identity
end N6.Weighted49
