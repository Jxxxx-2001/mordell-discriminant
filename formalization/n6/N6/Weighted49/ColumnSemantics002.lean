import N6.Weighted49.ColumnGround002
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column016_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column016Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column016Pairs column016Checked
  have hw : value x WA019 = 0 := by simpa only [actionData] using hWA 19
  simp only [column016Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column016Clearing column016Clearing_ne_zero _ h
theorem column016_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 16) = W (fun i => value x (basisData i)) (fun i => matrix_e i 16) := by
  have h := column016_value_zero x hWA
  rw [column016Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column016_identity
theorem column017_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column017Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column017Pairs column017Checked
  have hw : value x WA015 = 0 := by simpa only [actionData] using hWA 15
  simp only [column017Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column017Clearing column017Clearing_ne_zero _ h
theorem column017_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 17) = W (fun i => value x (basisData i)) (fun i => matrix_e i 17) := by
  have h := column017_value_zero x hWA
  rw [column017Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column017_identity
theorem column018_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column018Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column018Pairs column018Checked
  have hw : value x WA005 = 0 := by simpa only [actionData] using hWA 5
  simp only [column018Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column018Clearing column018Clearing_ne_zero _ h
theorem column018_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 18) = W (fun i => value x (basisData i)) (fun i => matrix_e i 18) := by
  have h := column018_value_zero x hWA
  rw [column018Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column018_identity
theorem column019_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column019Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column019Pairs column019Checked
  have hw : value x WA018 = 0 := by simpa only [actionData] using hWA 18
  simp only [column019Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column019Clearing column019Clearing_ne_zero _ h
theorem column019_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 19) = W (fun i => value x (basisData i)) (fun i => matrix_e i 19) := by
  have h := column019_value_zero x hWA
  rw [column019Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column019_identity
theorem column020_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column020Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column020Pairs column020Checked
  have hw : value x WA014 = 0 := by simpa only [actionData] using hWA 14
  simp only [column020Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column020Clearing column020Clearing_ne_zero _ h
theorem column020_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 20) = W (fun i => value x (basisData i)) (fun i => matrix_e i 20) := by
  have h := column020_value_zero x hWA
  rw [column020Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column020_identity
theorem column021_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column021Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column021Pairs column021Checked
  have hw : value x WA004 = 0 := by simpa only [actionData] using hWA 4
  simp only [column021Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column021Clearing column021Clearing_ne_zero _ h
theorem column021_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 21) = W (fun i => value x (basisData i)) (fun i => matrix_e i 21) := by
  have h := column021_value_zero x hWA
  rw [column021Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column021_identity
theorem column022_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column022Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column022Pairs column022Checked
  have hw : value x WA011 = 0 := by simpa only [actionData] using hWA 11
  simp only [column022Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column022Clearing column022Clearing_ne_zero _ h
theorem column022_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 22) = W (fun i => value x (basisData i)) (fun i => matrix_e i 22) := by
  have h := column022_value_zero x hWA
  rw [column022Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column022_identity
theorem column023_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column023Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column023Pairs column023Checked
  have hw : value x WA001 = 0 := by simpa only [actionData] using hWA 1
  simp only [column023Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column023Clearing column023Clearing_ne_zero _ h
theorem column023_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 23) = W (fun i => value x (basisData i)) (fun i => matrix_e i 23) := by
  have h := column023_value_zero x hWA
  rw [column023Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column023_identity
end N6.Weighted49
