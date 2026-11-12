import N6.Weighted49.ColumnGround004
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column032_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column032Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column032Pairs column032Checked
  simp only [column032Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column032Clearing column032Clearing_ne_zero _ h
theorem column032_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 32) = W (fun i => value x (basisData i)) (fun i => matrix_e i 32) := by
  have h := column032_value_zero x hWA
  rw [column032Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column032_identity
theorem column033_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column033Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column033Pairs column033Checked
  simp only [column033Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column033Clearing column033Clearing_ne_zero _ h
theorem column033_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 33) = W (fun i => value x (basisData i)) (fun i => matrix_e i 33) := by
  have h := column033_value_zero x hWA
  rw [column033Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column033_identity
theorem column034_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column034Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column034Pairs column034Checked
  simp only [column034Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column034Clearing column034Clearing_ne_zero _ h
theorem column034_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 34) = W (fun i => value x (basisData i)) (fun i => matrix_e i 34) := by
  have h := column034_value_zero x hWA
  rw [column034Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column034_identity
theorem column035_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column035Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column035Pairs column035Checked
  have hw : value x WA040 = 0 := by simpa only [actionData] using hWA 40
  simp only [column035Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column035Clearing column035Clearing_ne_zero _ h
theorem column035_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 35) = W (fun i => value x (basisData i)) (fun i => matrix_e i 35) := by
  have h := column035_value_zero x hWA
  rw [column035Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column035_identity
theorem column036_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column036Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column036Pairs column036Checked
  have hw : value x WA039 = 0 := by simpa only [actionData] using hWA 39
  simp only [column036Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column036Clearing column036Clearing_ne_zero _ h
theorem column036_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 36) = W (fun i => value x (basisData i)) (fun i => matrix_e i 36) := by
  have h := column036_value_zero x hWA
  rw [column036Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column036_identity
theorem column037_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column037Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column037Pairs column037Checked
  have hw : value x WA046 = 0 := by simpa only [actionData] using hWA 46
  simp only [column037Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column037Clearing column037Clearing_ne_zero _ h
theorem column037_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 37) = W (fun i => value x (basisData i)) (fun i => matrix_e i 37) := by
  have h := column037_value_zero x hWA
  rw [column037Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column037_identity
theorem column038_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column038Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column038Pairs column038Checked
  have hw : value x WA036 = 0 := by simpa only [actionData] using hWA 36
  simp only [column038Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column038Clearing column038Clearing_ne_zero _ h
theorem column038_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 38) = W (fun i => value x (basisData i)) (fun i => matrix_e i 38) := by
  have h := column038_value_zero x hWA
  rw [column038Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column038_identity
theorem column039_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column039Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column039Pairs column039Checked
  have hw : value x WA030 = 0 := by simpa only [actionData] using hWA 30
  simp only [column039Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column039Clearing column039Clearing_ne_zero _ h
theorem column039_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 39) = W (fun i => value x (basisData i)) (fun i => matrix_e i 39) := by
  have h := column039_value_zero x hWA
  rw [column039Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column039_identity
end N6.Weighted49
