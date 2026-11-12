import N6.Weighted49.ColumnGround023
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column184_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column184Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column184Pairs column184Checked
  have hw : value x WA033 = 0 := by simpa only [actionData] using hWA 33
  simp only [column184Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column184Clearing column184Clearing_ne_zero _ h
theorem column184_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 37) = W (fun i => value x (basisData i)) (fun i => matrix_B i 37) := by
  have h := column184_value_zero x hWA
  rw [column184Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column184_identity
theorem column185_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column185Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column185Pairs column185Checked
  have hw : value x WA027 = 0 := by simpa only [actionData] using hWA 27
  simp only [column185Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column185Clearing column185Clearing_ne_zero _ h
theorem column185_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 38) = W (fun i => value x (basisData i)) (fun i => matrix_B i 38) := by
  have h := column185_value_zero x hWA
  rw [column185Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column185_identity
theorem column186_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column186Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column186Pairs column186Checked
  have hw : value x WA024 = 0 := by simpa only [actionData] using hWA 24
  simp only [column186Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column186Clearing column186Clearing_ne_zero _ h
theorem column186_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 39) = W (fun i => value x (basisData i)) (fun i => matrix_B i 39) := by
  have h := column186_value_zero x hWA
  rw [column186Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column186_identity
theorem column187_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column187Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column187Pairs column187Checked
  have hw : value x WA034 = 0 := by simpa only [actionData] using hWA 34
  simp only [column187Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column187Clearing column187Clearing_ne_zero _ h
theorem column187_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 40) = W (fun i => value x (basisData i)) (fun i => matrix_B i 40) := by
  have h := column187_value_zero x hWA
  rw [column187Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column187_identity
theorem column188_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column188Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column188Pairs column188Checked
  have hw : value x WA028 = 0 := by simpa only [actionData] using hWA 28
  simp only [column188Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column188Clearing column188Clearing_ne_zero _ h
theorem column188_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 41) = W (fun i => value x (basisData i)) (fun i => matrix_B i 41) := by
  have h := column188_value_zero x hWA
  rw [column188Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column188_identity
theorem column189_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column189Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column189Pairs column189Checked
  have hw : value x WA032 = 0 := by simpa only [actionData] using hWA 32
  simp only [column189Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column189Clearing column189Clearing_ne_zero _ h
theorem column189_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 42) = W (fun i => value x (basisData i)) (fun i => matrix_B i 42) := by
  have h := column189_value_zero x hWA
  rw [column189Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column189_identity
theorem column190_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column190Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column190Pairs column190Checked
  have hw : value x WA026 = 0 := by simpa only [actionData] using hWA 26
  simp only [column190Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column190Clearing column190Clearing_ne_zero _ h
theorem column190_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 43) = W (fun i => value x (basisData i)) (fun i => matrix_B i 43) := by
  have h := column190_value_zero x hWA
  rw [column190Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column190_identity
theorem column191_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column191Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column191Pairs column191Checked
  have hw : value x WA023 = 0 := by simpa only [actionData] using hWA 23
  simp only [column191Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column191Clearing column191Clearing_ne_zero _ h
theorem column191_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 44) = W (fun i => value x (basisData i)) (fun i => matrix_B i 44) := by
  have h := column191_value_zero x hWA
  rw [column191Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column191_identity
end N6.Weighted49
