import N6.Weighted49.ColumnGround013
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column104_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column104Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column104Pairs column104Checked
  simp only [column104Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column104Clearing column104Clearing_ne_zero _ h
theorem column104_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 6) = W (fun i => value x (basisData i)) (fun i => matrix_c i 6) := by
  have h := column104_value_zero x hWA
  rw [column104Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column104_identity
theorem column105_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column105Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column105Pairs column105Checked
  simp only [column105Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column105Clearing column105Clearing_ne_zero _ h
theorem column105_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 7) = W (fun i => value x (basisData i)) (fun i => matrix_c i 7) := by
  have h := column105_value_zero x hWA
  rw [column105Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column105_identity
theorem column106_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column106Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column106Pairs column106Checked
  simp only [column106Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column106Clearing column106Clearing_ne_zero _ h
theorem column106_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 8) = W (fun i => value x (basisData i)) (fun i => matrix_c i 8) := by
  have h := column106_value_zero x hWA
  rw [column106Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column106_identity
theorem column107_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column107Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column107Pairs column107Checked
  simp only [column107Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column107Clearing column107Clearing_ne_zero _ h
theorem column107_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 9) = W (fun i => value x (basisData i)) (fun i => matrix_c i 9) := by
  have h := column107_value_zero x hWA
  rw [column107Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column107_identity
theorem column108_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column108Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column108Pairs column108Checked
  simp only [column108Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column108Clearing column108Clearing_ne_zero _ h
theorem column108_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 10) = W (fun i => value x (basisData i)) (fun i => matrix_c i 10) := by
  have h := column108_value_zero x hWA
  rw [column108Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column108_identity
theorem column109_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column109Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column109Pairs column109Checked
  simp only [column109Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column109Clearing column109Clearing_ne_zero _ h
theorem column109_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 11) = W (fun i => value x (basisData i)) (fun i => matrix_c i 11) := by
  have h := column109_value_zero x hWA
  rw [column109Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column109_identity
theorem column110_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column110Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column110Pairs column110Checked
  simp only [column110Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column110Clearing column110Clearing_ne_zero _ h
theorem column110_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 12) = W (fun i => value x (basisData i)) (fun i => matrix_c i 12) := by
  have h := column110_value_zero x hWA
  rw [column110Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column110_identity
theorem column111_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column111Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column111Pairs column111Checked
  simp only [column111Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column111Clearing column111Clearing_ne_zero _ h
theorem column111_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 13) = W (fun i => value x (basisData i)) (fun i => matrix_c i 13) := by
  have h := column111_value_zero x hWA
  rw [column111Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column111_identity
end N6.Weighted49
