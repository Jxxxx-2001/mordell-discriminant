import N6.Weighted49.ColumnGround019
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column152_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column152Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column152Pairs column152Checked
  simp only [column152Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column152Clearing column152Clearing_ne_zero _ h
theorem column152_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 5) = W (fun i => value x (basisData i)) (fun i => matrix_B i 5) := by
  have h := column152_value_zero x hWA
  rw [column152Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column152_identity
theorem column153_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column153Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column153Pairs column153Checked
  simp only [column153Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column153Clearing column153Clearing_ne_zero _ h
theorem column153_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 6) = W (fun i => value x (basisData i)) (fun i => matrix_B i 6) := by
  have h := column153_value_zero x hWA
  rw [column153Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column153_identity
theorem column154_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column154Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column154Pairs column154Checked
  simp only [column154Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column154Clearing column154Clearing_ne_zero _ h
theorem column154_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 7) = W (fun i => value x (basisData i)) (fun i => matrix_B i 7) := by
  have h := column154_value_zero x hWA
  rw [column154Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column154_identity
theorem column155_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column155Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column155Pairs column155Checked
  simp only [column155Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column155Clearing column155Clearing_ne_zero _ h
theorem column155_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 8) = W (fun i => value x (basisData i)) (fun i => matrix_B i 8) := by
  have h := column155_value_zero x hWA
  rw [column155Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column155_identity
theorem column156_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column156Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column156Pairs column156Checked
  simp only [column156Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column156Clearing column156Clearing_ne_zero _ h
theorem column156_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 9) = W (fun i => value x (basisData i)) (fun i => matrix_B i 9) := by
  have h := column156_value_zero x hWA
  rw [column156Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column156_identity
theorem column157_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column157Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column157Pairs column157Checked
  simp only [column157Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column157Clearing column157Clearing_ne_zero _ h
theorem column157_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 10) = W (fun i => value x (basisData i)) (fun i => matrix_B i 10) := by
  have h := column157_value_zero x hWA
  rw [column157Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column157_identity
theorem column158_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column158Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column158Pairs column158Checked
  simp only [column158Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column158Clearing column158Clearing_ne_zero _ h
theorem column158_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 11) = W (fun i => value x (basisData i)) (fun i => matrix_B i 11) := by
  have h := column158_value_zero x hWA
  rw [column158Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column158_identity
theorem column159_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column159Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column159Pairs column159Checked
  simp only [column159Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column159Clearing column159Clearing_ne_zero _ h
theorem column159_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 12) = W (fun i => value x (basisData i)) (fun i => matrix_B i 12) := by
  have h := column159_value_zero x hWA
  rw [column159Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column159_identity
end N6.Weighted49
