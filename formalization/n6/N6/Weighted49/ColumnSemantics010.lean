import N6.Weighted49.ColumnGround010
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column080_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column080Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column080Pairs column080Checked
  have hw : value x WA007 = 0 := by simpa only [actionData] using hWA 7
  simp only [column080Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column080Clearing column080Clearing_ne_zero _ h
theorem column080_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 31) = W (fun i => value x (basisData i)) (fun i => matrix_k i 31) := by
  have h := column080_value_zero x hWA
  rw [column080Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column080_identity
theorem column081_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column081Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column081Pairs column081Checked
  simp only [column081Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column081Clearing column081Clearing_ne_zero _ h
theorem column081_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 32) = W (fun i => value x (basisData i)) (fun i => matrix_k i 32) := by
  have h := column081_value_zero x hWA
  rw [column081Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column081_identity
theorem column082_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column082Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column082Pairs column082Checked
  simp only [column082Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column082Clearing column082Clearing_ne_zero _ h
theorem column082_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 33) = W (fun i => value x (basisData i)) (fun i => matrix_k i 33) := by
  have h := column082_value_zero x hWA
  rw [column082Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column082_identity
theorem column083_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column083Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column083Pairs column083Checked
  simp only [column083Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column083Clearing column083Clearing_ne_zero _ h
theorem column083_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 34) = W (fun i => value x (basisData i)) (fun i => matrix_k i 34) := by
  have h := column083_value_zero x hWA
  rw [column083Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column083_identity
theorem column084_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column084Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column084Pairs column084Checked
  have hw : value x WA039 = 0 := by simpa only [actionData] using hWA 39
  simp only [column084Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column084Clearing column084Clearing_ne_zero _ h
theorem column084_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 35) = W (fun i => value x (basisData i)) (fun i => matrix_k i 35) := by
  have h := column084_value_zero x hWA
  rw [column084Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column084_identity
theorem column085_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column085Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column085Pairs column085Checked
  have hw : value x WA038 = 0 := by simpa only [actionData] using hWA 38
  simp only [column085Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column085Clearing column085Clearing_ne_zero _ h
theorem column085_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 36) = W (fun i => value x (basisData i)) (fun i => matrix_k i 36) := by
  have h := column085_value_zero x hWA
  rw [column085Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column085_identity
theorem column086_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column086Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column086Pairs column086Checked
  have hw : value x WA045 = 0 := by simpa only [actionData] using hWA 45
  simp only [column086Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column086Clearing column086Clearing_ne_zero _ h
theorem column086_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 37) = W (fun i => value x (basisData i)) (fun i => matrix_k i 37) := by
  have h := column086_value_zero x hWA
  rw [column086Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column086_identity
theorem column087_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column087Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column087Pairs column087Checked
  have hw : value x WA035 = 0 := by simpa only [actionData] using hWA 35
  simp only [column087Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column087Clearing column087Clearing_ne_zero _ h
theorem column087_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 38) = W (fun i => value x (basisData i)) (fun i => matrix_k i 38) := by
  have h := column087_value_zero x hWA
  rw [column087Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column087_identity
end N6.Weighted49
