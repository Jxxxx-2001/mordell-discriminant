import N6.Weighted49.ColumnGround024
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column192_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column192Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column192Pairs column192Checked
  have hw : value x WA031 = 0 := by simpa only [actionData] using hWA 31
  simp only [column192Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column192Clearing column192Clearing_ne_zero _ h
theorem column192_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 45) = W (fun i => value x (basisData i)) (fun i => matrix_B i 45) := by
  have h := column192_value_zero x hWA
  rw [column192Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column192_identity
theorem column193_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column193Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column193Pairs column193Checked
  have hw : value x WA025 = 0 := by simpa only [actionData] using hWA 25
  simp only [column193Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column193Clearing column193Clearing_ne_zero _ h
theorem column193_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 46) = W (fun i => value x (basisData i)) (fun i => matrix_B i 46) := by
  have h := column193_value_zero x hWA
  rw [column193Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column193_identity
theorem column194_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column194Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column194Pairs column194Checked
  have hw : value x WA022 = 0 := by simpa only [actionData] using hWA 22
  simp only [column194Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column194Clearing column194Clearing_ne_zero _ h
theorem column194_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 47) = W (fun i => value x (basisData i)) (fun i => matrix_B i 47) := by
  have h := column194_value_zero x hWA
  rw [column194Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column194_identity
theorem column195_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column195Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column195Pairs column195Checked
  have hw : value x WA021 = 0 := by simpa only [actionData] using hWA 21
  simp only [column195Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column195Clearing column195Clearing_ne_zero _ h
theorem column195_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 48) = W (fun i => value x (basisData i)) (fun i => matrix_B i 48) := by
  have h := column195_value_zero x hWA
  rw [column195Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column195_identity
end N6.Weighted49
