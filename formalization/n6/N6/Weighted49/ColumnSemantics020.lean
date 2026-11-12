import N6.Weighted49.ColumnGround020
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column160_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column160Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column160Pairs column160Checked
  simp only [column160Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column160Clearing column160Clearing_ne_zero _ h
theorem column160_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 13) = W (fun i => value x (basisData i)) (fun i => matrix_B i 13) := by
  have h := column160_value_zero x hWA
  rw [column160Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column160_identity
theorem column161_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column161Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column161Pairs column161Checked
  simp only [column161Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column161Clearing column161Clearing_ne_zero _ h
theorem column161_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 14) = W (fun i => value x (basisData i)) (fun i => matrix_B i 14) := by
  have h := column161_value_zero x hWA
  rw [column161Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column161_identity
theorem column162_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column162Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column162Pairs column162Checked
  have hw : value x WA005 = 0 := by simpa only [actionData] using hWA 5
  simp only [column162Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column162Clearing column162Clearing_ne_zero _ h
theorem column162_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 15) = W (fun i => value x (basisData i)) (fun i => matrix_B i 15) := by
  have h := column162_value_zero x hWA
  rw [column162Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column162_identity
theorem column163_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column163Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column163Pairs column163Checked
  have hw : value x WA004 = 0 := by simpa only [actionData] using hWA 4
  simp only [column163Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column163Clearing column163Clearing_ne_zero _ h
theorem column163_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 16) = W (fun i => value x (basisData i)) (fun i => matrix_B i 16) := by
  have h := column163_value_zero x hWA
  rw [column163Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column163_identity
theorem column164_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column164Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column164Pairs column164Checked
  have hw : value x WA001 = 0 := by simpa only [actionData] using hWA 1
  simp only [column164Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column164Clearing column164Clearing_ne_zero _ h
theorem column164_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 17) = W (fun i => value x (basisData i)) (fun i => matrix_B i 17) := by
  have h := column164_value_zero x hWA
  rw [column164Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column164_identity
theorem column165_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column165Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column165Pairs column165Checked
  simp only [column165Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column165Clearing column165Clearing_ne_zero _ h
theorem column165_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 18) = W (fun i => value x (basisData i)) (fun i => matrix_B i 18) := by
  have h := column165_value_zero x hWA
  rw [column165Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column165_identity
theorem column166_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column166Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column166Pairs column166Checked
  have hw : value x WA003 = 0 := by simpa only [actionData] using hWA 3
  simp only [column166Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column166Clearing column166Clearing_ne_zero _ h
theorem column166_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 19) = W (fun i => value x (basisData i)) (fun i => matrix_B i 19) := by
  have h := column166_value_zero x hWA
  rw [column166Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column166_identity
theorem column167_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column167Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column167Pairs column167Checked
  have hw : value x WA000 = 0 := by simpa only [actionData] using hWA 0
  simp only [column167Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column167Clearing column167Clearing_ne_zero _ h
theorem column167_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 20) = W (fun i => value x (basisData i)) (fun i => matrix_B i 20) := by
  have h := column167_value_zero x hWA
  rw [column167Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column167_identity
end N6.Weighted49
