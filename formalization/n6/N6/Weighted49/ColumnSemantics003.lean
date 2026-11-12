import N6.Weighted49.ColumnGround003
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column024_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column024Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column024Pairs column024Checked
  simp only [column024Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column024Clearing column024Clearing_ne_zero _ h
theorem column024_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 24) = W (fun i => value x (basisData i)) (fun i => matrix_e i 24) := by
  have h := column024_value_zero x hWA
  rw [column024Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column024_identity
theorem column025_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column025Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column025Pairs column025Checked
  have hw : value x WA017 = 0 := by simpa only [actionData] using hWA 17
  simp only [column025Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column025Clearing column025Clearing_ne_zero _ h
theorem column025_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 25) = W (fun i => value x (basisData i)) (fun i => matrix_e i 25) := by
  have h := column025_value_zero x hWA
  rw [column025Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column025_identity
theorem column026_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column026Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column026Pairs column026Checked
  have hw : value x WA013 = 0 := by simpa only [actionData] using hWA 13
  simp only [column026Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column026Clearing column026Clearing_ne_zero _ h
theorem column026_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 26) = W (fun i => value x (basisData i)) (fun i => matrix_e i 26) := by
  have h := column026_value_zero x hWA
  rw [column026Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column026_identity
theorem column027_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column027Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column027Pairs column027Checked
  have hw : value x WA003 = 0 := by simpa only [actionData] using hWA 3
  simp only [column027Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column027Clearing column027Clearing_ne_zero _ h
theorem column027_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 27) = W (fun i => value x (basisData i)) (fun i => matrix_e i 27) := by
  have h := column027_value_zero x hWA
  rw [column027Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column027_identity
theorem column028_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column028Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column028Pairs column028Checked
  have hw : value x WA010 = 0 := by simpa only [actionData] using hWA 10
  simp only [column028Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column028Clearing column028Clearing_ne_zero _ h
theorem column028_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 28) = W (fun i => value x (basisData i)) (fun i => matrix_e i 28) := by
  have h := column028_value_zero x hWA
  rw [column028Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column028_identity
theorem column029_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column029Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column029Pairs column029Checked
  have hw : value x WA000 = 0 := by simpa only [actionData] using hWA 0
  simp only [column029Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column029Clearing column029Clearing_ne_zero _ h
theorem column029_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 29) = W (fun i => value x (basisData i)) (fun i => matrix_e i 29) := by
  have h := column029_value_zero x hWA
  rw [column029Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column029_identity
theorem column030_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column030Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column030Pairs column030Checked
  simp only [column030Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column030Clearing column030Clearing_ne_zero _ h
theorem column030_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 30) = W (fun i => value x (basisData i)) (fun i => matrix_e i 30) := by
  have h := column030_value_zero x hWA
  rw [column030Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column030_identity
theorem column031_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column031Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column031Pairs column031Checked
  have hw : value x WA008 = 0 := by simpa only [actionData] using hWA 8
  simp only [column031Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column031Clearing column031Clearing_ne_zero _ h
theorem column031_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 31) = W (fun i => value x (basisData i)) (fun i => matrix_e i 31) := by
  have h := column031_value_zero x hWA
  rw [column031Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column031_identity
end N6.Weighted49
