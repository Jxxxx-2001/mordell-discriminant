import N6.Weighted49.ColumnGround017
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column136_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column136Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column136Pairs column136Checked
  have hw : value x WA033 = 0 := by simpa only [actionData] using hWA 33
  simp only [column136Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column136Clearing column136Clearing_ne_zero _ h
theorem column136_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 38) = W (fun i => value x (basisData i)) (fun i => matrix_c i 38) := by
  have h := column136_value_zero x hWA
  rw [column136Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column136_identity
theorem column137_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column137Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column137Pairs column137Checked
  have hw : value x WA027 = 0 := by simpa only [actionData] using hWA 27
  simp only [column137Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column137Clearing column137Clearing_ne_zero _ h
theorem column137_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 39) = W (fun i => value x (basisData i)) (fun i => matrix_c i 39) := by
  have h := column137_value_zero x hWA
  rw [column137Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column137_identity
theorem column138_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column138Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column138Pairs column138Checked
  have hw : value x WA044 = 0 := by simpa only [actionData] using hWA 44
  simp only [column138Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column138Clearing column138Clearing_ne_zero _ h
theorem column138_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 40) = W (fun i => value x (basisData i)) (fun i => matrix_c i 40) := by
  have h := column138_value_zero x hWA
  rw [column138Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column138_identity
theorem column139_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column139Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column139Pairs column139Checked
  have hw : value x WA034 = 0 := by simpa only [actionData] using hWA 34
  simp only [column139Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column139Clearing column139Clearing_ne_zero _ h
theorem column139_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 41) = W (fun i => value x (basisData i)) (fun i => matrix_c i 41) := by
  have h := column139_value_zero x hWA
  rw [column139Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column139_identity
theorem column140_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column140Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column140Pairs column140Checked
  have hw : value x WA042 = 0 := by simpa only [actionData] using hWA 42
  simp only [column140Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column140Clearing column140Clearing_ne_zero _ h
theorem column140_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 42) = W (fun i => value x (basisData i)) (fun i => matrix_c i 42) := by
  have h := column140_value_zero x hWA
  rw [column140Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column140_identity
theorem column141_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column141Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column141Pairs column141Checked
  have hw : value x WA032 = 0 := by simpa only [actionData] using hWA 32
  simp only [column141Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column141Clearing column141Clearing_ne_zero _ h
theorem column141_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 43) = W (fun i => value x (basisData i)) (fun i => matrix_c i 43) := by
  have h := column141_value_zero x hWA
  rw [column141Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column141_identity
theorem column142_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column142Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column142Pairs column142Checked
  have hw : value x WA026 = 0 := by simpa only [actionData] using hWA 26
  simp only [column142Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column142Clearing column142Clearing_ne_zero _ h
theorem column142_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 44) = W (fun i => value x (basisData i)) (fun i => matrix_c i 44) := by
  have h := column142_value_zero x hWA
  rw [column142Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column142_identity
theorem column143_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column143Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column143Pairs column143Checked
  have hw : value x WA041 = 0 := by simpa only [actionData] using hWA 41
  simp only [column143Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column143Clearing column143Clearing_ne_zero _ h
theorem column143_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 45) = W (fun i => value x (basisData i)) (fun i => matrix_c i 45) := by
  have h := column143_value_zero x hWA
  rw [column143Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column143_identity
end N6.Weighted49
