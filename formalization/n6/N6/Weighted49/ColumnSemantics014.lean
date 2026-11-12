import N6.Weighted49.ColumnGround014
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column112_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column112Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column112Pairs column112Checked
  simp only [column112Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column112Clearing column112Clearing_ne_zero _ h
theorem column112_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 14) = W (fun i => value x (basisData i)) (fun i => matrix_c i 14) := by
  have h := column112_value_zero x hWA
  rw [column112Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column112_identity
theorem column113_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column113Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column113Pairs column113Checked
  have hw : value x WA015 = 0 := by simpa only [actionData] using hWA 15
  simp only [column113Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column113Clearing column113Clearing_ne_zero _ h
theorem column113_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 15) = W (fun i => value x (basisData i)) (fun i => matrix_c i 15) := by
  have h := column113_value_zero x hWA
  rw [column113Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column113_identity
theorem column114_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column114Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column114Pairs column114Checked
  have hw : value x WA014 = 0 := by simpa only [actionData] using hWA 14
  simp only [column114Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column114Clearing column114Clearing_ne_zero _ h
theorem column114_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 16) = W (fun i => value x (basisData i)) (fun i => matrix_c i 16) := by
  have h := column114_value_zero x hWA
  rw [column114Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column114_identity
theorem column115_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column115Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column115Pairs column115Checked
  have hw : value x WA011 = 0 := by simpa only [actionData] using hWA 11
  simp only [column115Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column115Clearing column115Clearing_ne_zero _ h
theorem column115_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 17) = W (fun i => value x (basisData i)) (fun i => matrix_c i 17) := by
  have h := column115_value_zero x hWA
  rw [column115Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column115_identity
theorem column116_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column116Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column116Pairs column116Checked
  have hw : value x WA001 = 0 := by simpa only [actionData] using hWA 1
  simp only [column116Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column116Clearing column116Clearing_ne_zero _ h
theorem column116_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 18) = W (fun i => value x (basisData i)) (fun i => matrix_c i 18) := by
  have h := column116_value_zero x hWA
  rw [column116Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column116_identity
theorem column117_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column117Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column117Pairs column117Checked
  have hw : value x WA013 = 0 := by simpa only [actionData] using hWA 13
  simp only [column117Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column117Clearing column117Clearing_ne_zero _ h
theorem column117_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 19) = W (fun i => value x (basisData i)) (fun i => matrix_c i 19) := by
  have h := column117_value_zero x hWA
  rw [column117Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column117_identity
theorem column118_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column118Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column118Pairs column118Checked
  have hw : value x WA010 = 0 := by simpa only [actionData] using hWA 10
  simp only [column118Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column118Clearing column118Clearing_ne_zero _ h
theorem column118_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 20) = W (fun i => value x (basisData i)) (fun i => matrix_c i 20) := by
  have h := column118_value_zero x hWA
  rw [column118Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column118_identity
theorem column119_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column119Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column119Pairs column119Checked
  have hw : value x WA000 = 0 := by simpa only [actionData] using hWA 0
  simp only [column119Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column119Clearing column119Clearing_ne_zero _ h
theorem column119_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 21) = W (fun i => value x (basisData i)) (fun i => matrix_c i 21) := by
  have h := column119_value_zero x hWA
  rw [column119Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column119_identity
end N6.Weighted49
