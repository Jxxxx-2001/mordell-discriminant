import N6.Weighted49.ColumnGround018
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column144_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column144Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column144Pairs column144Checked
  have hw : value x WA031 = 0 := by simpa only [actionData] using hWA 31
  simp only [column144Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column144Clearing column144Clearing_ne_zero _ h
theorem column144_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 46) = W (fun i => value x (basisData i)) (fun i => matrix_c i 46) := by
  have h := column144_value_zero x hWA
  rw [column144Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column144_identity
theorem column145_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column145Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column145Pairs column145Checked
  have hw : value x WA025 = 0 := by simpa only [actionData] using hWA 25
  simp only [column145Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column145Clearing column145Clearing_ne_zero _ h
theorem column145_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 47) = W (fun i => value x (basisData i)) (fun i => matrix_c i 47) := by
  have h := column145_value_zero x hWA
  rw [column145Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column145_identity
theorem column146_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column146Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column146Pairs column146Checked
  have hw : value x WA022 = 0 := by simpa only [actionData] using hWA 22
  simp only [column146Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column146Clearing column146Clearing_ne_zero _ h
theorem column146_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_cDen : R) * x 3 * value x (basisData 48) = W (fun i => value x (basisData i)) (fun i => matrix_c i 48) := by
  have h := column146_value_zero x hWA
  rw [column146Poly, value_columnPoly x _ _ (variableMon_value_3 x)] at h
  exact sub_eq_zero.mp h
#print axioms column146_identity
theorem column147_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column147Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column147Pairs column147Checked
  simp only [column147Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column147Clearing column147Clearing_ne_zero _ h
theorem column147_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 0) = W (fun i => value x (basisData i)) (fun i => matrix_B i 0) := by
  have h := column147_value_zero x hWA
  rw [column147Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column147_identity
theorem column148_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column148Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column148Pairs column148Checked
  simp only [column148Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column148Clearing column148Clearing_ne_zero _ h
theorem column148_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 1) = W (fun i => value x (basisData i)) (fun i => matrix_B i 1) := by
  have h := column148_value_zero x hWA
  rw [column148Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column148_identity
theorem column149_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column149Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column149Pairs column149Checked
  simp only [column149Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column149Clearing column149Clearing_ne_zero _ h
theorem column149_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 2) = W (fun i => value x (basisData i)) (fun i => matrix_B i 2) := by
  have h := column149_value_zero x hWA
  rw [column149Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column149_identity
theorem column150_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column150Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column150Pairs column150Checked
  simp only [column150Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column150Clearing column150Clearing_ne_zero _ h
theorem column150_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 3) = W (fun i => value x (basisData i)) (fun i => matrix_B i 3) := by
  have h := column150_value_zero x hWA
  rw [column150Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column150_identity
theorem column151_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column151Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column151Pairs column151Checked
  simp only [column151Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column151Clearing column151Clearing_ne_zero _ h
theorem column151_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 4) = W (fun i => value x (basisData i)) (fun i => matrix_B i 4) := by
  have h := column151_value_zero x hWA
  rw [column151Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column151_identity
end N6.Weighted49
