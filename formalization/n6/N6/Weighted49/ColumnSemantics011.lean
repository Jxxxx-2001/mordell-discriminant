import N6.Weighted49.ColumnGround011
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column088_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column088Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column088Pairs column088Checked
  have hw : value x WA029 = 0 := by simpa only [actionData] using hWA 29
  simp only [column088Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column088Clearing column088Clearing_ne_zero _ h
theorem column088_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 39) = W (fun i => value x (basisData i)) (fun i => matrix_k i 39) := by
  have h := column088_value_zero x hWA
  rw [column088Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column088_identity
theorem column089_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column089Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column089Pairs column089Checked
  have hw : value x WA047 = 0 := by simpa only [actionData] using hWA 47
  simp only [column089Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column089Clearing column089Clearing_ne_zero _ h
theorem column089_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 40) = W (fun i => value x (basisData i)) (fun i => matrix_k i 40) := by
  have h := column089_value_zero x hWA
  rw [column089Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column089_identity
theorem column090_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column090Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column090Pairs column090Checked
  have hw : value x WA037 = 0 := by simpa only [actionData] using hWA 37
  simp only [column090Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column090Clearing column090Clearing_ne_zero _ h
theorem column090_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 41) = W (fun i => value x (basisData i)) (fun i => matrix_k i 41) := by
  have h := column090_value_zero x hWA
  rw [column090Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column090_identity
theorem column091_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column091Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column091Pairs column091Checked
  have hw : value x WA044 = 0 := by simpa only [actionData] using hWA 44
  simp only [column091Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column091Clearing column091Clearing_ne_zero _ h
theorem column091_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 42) = W (fun i => value x (basisData i)) (fun i => matrix_k i 42) := by
  have h := column091_value_zero x hWA
  rw [column091Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column091_identity
theorem column092_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column092Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column092Pairs column092Checked
  have hw : value x WA034 = 0 := by simpa only [actionData] using hWA 34
  simp only [column092Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column092Clearing column092Clearing_ne_zero _ h
theorem column092_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 43) = W (fun i => value x (basisData i)) (fun i => matrix_k i 43) := by
  have h := column092_value_zero x hWA
  rw [column092Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column092_identity
theorem column093_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column093Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column093Pairs column093Checked
  have hw : value x WA028 = 0 := by simpa only [actionData] using hWA 28
  simp only [column093Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column093Clearing column093Clearing_ne_zero _ h
theorem column093_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 44) = W (fun i => value x (basisData i)) (fun i => matrix_k i 44) := by
  have h := column093_value_zero x hWA
  rw [column093Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column093_identity
theorem column094_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column094Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column094Pairs column094Checked
  have hw : value x WA042 = 0 := by simpa only [actionData] using hWA 42
  simp only [column094Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column094Clearing column094Clearing_ne_zero _ h
theorem column094_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 45) = W (fun i => value x (basisData i)) (fun i => matrix_k i 45) := by
  have h := column094_value_zero x hWA
  rw [column094Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column094_identity
theorem column095_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column095Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column095Pairs column095Checked
  have hw : value x WA032 = 0 := by simpa only [actionData] using hWA 32
  simp only [column095Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column095Clearing column095Clearing_ne_zero _ h
theorem column095_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_kDen : R) * x 2 * value x (basisData 46) = W (fun i => value x (basisData i)) (fun i => matrix_k i 46) := by
  have h := column095_value_zero x hWA
  rw [column095Poly, value_columnPoly x _ _ (variableMon_value_2 x)] at h
  exact sub_eq_zero.mp h
#print axioms column095_identity
end N6.Weighted49
