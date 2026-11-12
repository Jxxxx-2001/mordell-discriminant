import N6.Weighted49.ColumnGround012
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column096_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column096Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column096Pairs column096Checked
  have hw : value x WA026 = 0 := by simpa only [actionData] using hWA 26
  simp only [column096Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column096Clearing column096Clearing_ne_zero _ h
theorem column096_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 47) = W (fun i => value x (basisData i)) (fun i => matrix_k i 47) := by
  have h := column096_value_zero x hWA
  rw [column096Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column096_identity
theorem column097_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column097Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column097Pairs column097Checked
  have hw : value x WA023 = 0 := by simpa only [actionData] using hWA 23
  simp only [column097Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column097Clearing column097Clearing_ne_zero _ h
theorem column097_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 48) = W (fun i => value x (basisData i)) (fun i => matrix_k i 48) := by
  have h := column097_value_zero x hWA
  rw [column097Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column097_identity
theorem column098_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column098Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column098Pairs column098Checked
  simp only [column098Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column098Clearing column098Clearing_ne_zero _ h
theorem column098_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 0) = W (fun i => value x (basisData i)) (fun i => matrix_c i 0) := by
  have h := column098_value_zero x hWA
  rw [column098Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column098_identity
theorem column099_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column099Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column099Pairs column099Checked
  simp only [column099Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column099Clearing column099Clearing_ne_zero _ h
theorem column099_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 1) = W (fun i => value x (basisData i)) (fun i => matrix_c i 1) := by
  have h := column099_value_zero x hWA
  rw [column099Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column099_identity
theorem column100_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column100Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column100Pairs column100Checked
  simp only [column100Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column100Clearing column100Clearing_ne_zero _ h
theorem column100_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 2) = W (fun i => value x (basisData i)) (fun i => matrix_c i 2) := by
  have h := column100_value_zero x hWA
  rw [column100Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column100_identity
theorem column101_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column101Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column101Pairs column101Checked
  simp only [column101Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column101Clearing column101Clearing_ne_zero _ h
theorem column101_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 3) = W (fun i => value x (basisData i)) (fun i => matrix_c i 3) := by
  have h := column101_value_zero x hWA
  rw [column101Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column101_identity
theorem column102_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column102Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column102Pairs column102Checked
  simp only [column102Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column102Clearing column102Clearing_ne_zero _ h
theorem column102_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 4) = W (fun i => value x (basisData i)) (fun i => matrix_c i 4) := by
  have h := column102_value_zero x hWA
  rw [column102Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column102_identity
theorem column103_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column103Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column103Pairs column103Checked
  simp only [column103Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column103Clearing column103Clearing_ne_zero _ h
theorem column103_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 5) = W (fun i => value x (basisData i)) (fun i => matrix_c i 5) := by
  have h := column103_value_zero x hWA
  rw [column103Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column103_identity
end N6.Weighted49
