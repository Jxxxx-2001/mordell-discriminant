import N6.Weighted49.ColumnGround022
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column176_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column176Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column176Pairs column176Checked
  simp only [column176Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column176Clearing column176Clearing_ne_zero _ h
theorem column176_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 29) = W (fun i => value x (basisData i)) (fun i => matrix_B i 29) := by
  have h := column176_value_zero x hWA
  rw [column176Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column176_identity
theorem column177_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column177Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column177Pairs column177Checked
  simp only [column177Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column177Clearing column177Clearing_ne_zero _ h
theorem column177_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 30) = W (fun i => value x (basisData i)) (fun i => matrix_B i 30) := by
  have h := column177_value_zero x hWA
  rw [column177Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column177_identity
theorem column178_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column178Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column178Pairs column178Checked
  simp only [column178Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column178Clearing column178Clearing_ne_zero _ h
theorem column178_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 31) = W (fun i => value x (basisData i)) (fun i => matrix_B i 31) := by
  have h := column178_value_zero x hWA
  rw [column178Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column178_identity
theorem column179_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column179Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column179Pairs column179Checked
  simp only [column179Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column179Clearing column179Clearing_ne_zero _ h
theorem column179_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 32) = W (fun i => value x (basisData i)) (fun i => matrix_B i 32) := by
  have h := column179_value_zero x hWA
  rw [column179Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column179_identity
theorem column180_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column180Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column180Pairs column180Checked
  simp only [column180Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column180Clearing column180Clearing_ne_zero _ h
theorem column180_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 33) = W (fun i => value x (basisData i)) (fun i => matrix_B i 33) := by
  have h := column180_value_zero x hWA
  rw [column180Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column180_identity
theorem column181_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column181Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column181Pairs column181Checked
  simp only [column181Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column181Clearing column181Clearing_ne_zero _ h
theorem column181_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 34) = W (fun i => value x (basisData i)) (fun i => matrix_B i 34) := by
  have h := column181_value_zero x hWA
  rw [column181Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column181_identity
theorem column182_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column182Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column182Pairs column182Checked
  have hw : value x WA030 = 0 := by simpa only [actionData] using hWA 30
  simp only [column182Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column182Clearing column182Clearing_ne_zero _ h
theorem column182_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 35) = W (fun i => value x (basisData i)) (fun i => matrix_B i 35) := by
  have h := column182_value_zero x hWA
  rw [column182Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column182_identity
theorem column183_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column183Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column183Pairs column183Checked
  have hw : value x WA029 = 0 := by simpa only [actionData] using hWA 29
  simp only [column183Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column183Clearing column183Clearing_ne_zero _ h
theorem column183_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 36) = W (fun i => value x (basisData i)) (fun i => matrix_B i 36) := by
  have h := column183_value_zero x hWA
  rw [column183Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column183_identity
end N6.Weighted49
