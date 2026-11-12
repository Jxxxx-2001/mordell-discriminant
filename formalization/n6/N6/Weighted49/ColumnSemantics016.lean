import N6.Weighted49.ColumnGround016
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column128_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column128Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column128Pairs column128Checked
  simp only [column128Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column128Clearing column128Clearing_ne_zero _ h
theorem column128_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 30) = W (fun i => value x (basisData i)) (fun i => matrix_c i 30) := by
  have h := column128_value_zero x hWA
  rw [column128Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column128_identity
theorem column129_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column129Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column129Pairs column129Checked
  have hw : value x WA006 = 0 := by simpa only [actionData] using hWA 6
  simp only [column129Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column129Clearing column129Clearing_ne_zero _ h
theorem column129_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 31) = W (fun i => value x (basisData i)) (fun i => matrix_c i 31) := by
  have h := column129_value_zero x hWA
  rw [column129Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column129_identity
theorem column130_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column130Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column130Pairs column130Checked
  simp only [column130Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column130Clearing column130Clearing_ne_zero _ h
theorem column130_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 32) = W (fun i => value x (basisData i)) (fun i => matrix_c i 32) := by
  have h := column130_value_zero x hWA
  rw [column130Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column130_identity
theorem column131_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column131Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column131Pairs column131Checked
  simp only [column131Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column131Clearing column131Clearing_ne_zero _ h
theorem column131_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 33) = W (fun i => value x (basisData i)) (fun i => matrix_c i 33) := by
  have h := column131_value_zero x hWA
  rw [column131Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column131_identity
theorem column132_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column132Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column132Pairs column132Checked
  simp only [column132Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column132Clearing column132Clearing_ne_zero _ h
theorem column132_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 34) = W (fun i => value x (basisData i)) (fun i => matrix_c i 34) := by
  have h := column132_value_zero x hWA
  rw [column132Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column132_identity
theorem column133_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column133Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column133Pairs column133Checked
  have hw : value x WA036 = 0 := by simpa only [actionData] using hWA 36
  simp only [column133Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column133Clearing column133Clearing_ne_zero _ h
theorem column133_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 35) = W (fun i => value x (basisData i)) (fun i => matrix_c i 35) := by
  have h := column133_value_zero x hWA
  rw [column133Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column133_identity
theorem column134_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column134Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column134Pairs column134Checked
  have hw : value x WA035 = 0 := by simpa only [actionData] using hWA 35
  simp only [column134Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column134Clearing column134Clearing_ne_zero _ h
theorem column134_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 36) = W (fun i => value x (basisData i)) (fun i => matrix_c i 36) := by
  have h := column134_value_zero x hWA
  rw [column134Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column134_identity
theorem column135_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column135Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column135Pairs column135Checked
  have hw : value x WA043 = 0 := by simpa only [actionData] using hWA 43
  simp only [column135Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column135Clearing column135Clearing_ne_zero _ h
theorem column135_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 37) = W (fun i => value x (basisData i)) (fun i => matrix_c i 37) := by
  have h := column135_value_zero x hWA
  rw [column135Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column135_identity
end N6.Weighted49
