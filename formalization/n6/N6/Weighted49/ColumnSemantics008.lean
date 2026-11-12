import N6.Weighted49.ColumnGround008
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column064_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column064Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column064Pairs column064Checked
  have hw : value x WA019 = 0 := by simpa only [actionData] using hWA 19
  simp only [column064Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column064Clearing column064Clearing_ne_zero _ h
theorem column064_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 15) = W (fun i => value x (basisData i)) (fun i => matrix_k i 15) := by
  have h := column064_value_zero x hWA
  rw [column064Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column064_identity
theorem column065_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column065Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column065Pairs column065Checked
  have hw : value x WA018 = 0 := by simpa only [actionData] using hWA 18
  simp only [column065Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column065Clearing column065Clearing_ne_zero _ h
theorem column065_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 16) = W (fun i => value x (basisData i)) (fun i => matrix_k i 16) := by
  have h := column065_value_zero x hWA
  rw [column065Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column065_identity
theorem column066_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column066Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column066Pairs column066Checked
  have hw : value x WA014 = 0 := by simpa only [actionData] using hWA 14
  simp only [column066Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column066Clearing column066Clearing_ne_zero _ h
theorem column066_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 17) = W (fun i => value x (basisData i)) (fun i => matrix_k i 17) := by
  have h := column066_value_zero x hWA
  rw [column066Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column066_identity
theorem column067_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column067Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column067Pairs column067Checked
  have hw : value x WA004 = 0 := by simpa only [actionData] using hWA 4
  simp only [column067Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column067Clearing column067Clearing_ne_zero _ h
theorem column067_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 18) = W (fun i => value x (basisData i)) (fun i => matrix_k i 18) := by
  have h := column067_value_zero x hWA
  rw [column067Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column067_identity
theorem column068_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column068Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column068Pairs column068Checked
  have hw : value x WA017 = 0 := by simpa only [actionData] using hWA 17
  simp only [column068Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column068Clearing column068Clearing_ne_zero _ h
theorem column068_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 19) = W (fun i => value x (basisData i)) (fun i => matrix_k i 19) := by
  have h := column068_value_zero x hWA
  rw [column068Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column068_identity
theorem column069_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column069Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column069Pairs column069Checked
  have hw : value x WA013 = 0 := by simpa only [actionData] using hWA 13
  simp only [column069Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column069Clearing column069Clearing_ne_zero _ h
theorem column069_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 20) = W (fun i => value x (basisData i)) (fun i => matrix_k i 20) := by
  have h := column069_value_zero x hWA
  rw [column069Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column069_identity
theorem column070_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column070Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column070Pairs column070Checked
  have hw : value x WA003 = 0 := by simpa only [actionData] using hWA 3
  simp only [column070Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column070Clearing column070Clearing_ne_zero _ h
theorem column070_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 21) = W (fun i => value x (basisData i)) (fun i => matrix_k i 21) := by
  have h := column070_value_zero x hWA
  rw [column070Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column070_identity
theorem column071_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column071Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column071Pairs column071Checked
  have hw : value x WA010 = 0 := by simpa only [actionData] using hWA 10
  simp only [column071Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column071Clearing column071Clearing_ne_zero _ h
theorem column071_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 22) = W (fun i => value x (basisData i)) (fun i => matrix_k i 22) := by
  have h := column071_value_zero x hWA
  rw [column071Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column071_identity
end N6.Weighted49
