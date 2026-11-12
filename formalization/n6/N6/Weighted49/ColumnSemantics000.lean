import N6.Weighted49.ColumnGround000
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column000_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column000Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column000Pairs column000Checked
  simp only [column000Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column000Clearing column000Clearing_ne_zero _ h
theorem column000_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 0) = W (fun i => value x (basisData i)) (fun i => matrix_e i 0) := by
  have h := column000_value_zero x hWA
  rw [column000Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column000_identity
theorem column001_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column001Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column001Pairs column001Checked
  simp only [column001Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column001Clearing column001Clearing_ne_zero _ h
theorem column001_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 1) = W (fun i => value x (basisData i)) (fun i => matrix_e i 1) := by
  have h := column001_value_zero x hWA
  rw [column001Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column001_identity
theorem column002_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column002Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column002Pairs column002Checked
  simp only [column002Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column002Clearing column002Clearing_ne_zero _ h
theorem column002_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 2) = W (fun i => value x (basisData i)) (fun i => matrix_e i 2) := by
  have h := column002_value_zero x hWA
  rw [column002Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column002_identity
theorem column003_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column003Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column003Pairs column003Checked
  simp only [column003Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column003Clearing column003Clearing_ne_zero _ h
theorem column003_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 3) = W (fun i => value x (basisData i)) (fun i => matrix_e i 3) := by
  have h := column003_value_zero x hWA
  rw [column003Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column003_identity
theorem column004_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column004Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column004Pairs column004Checked
  simp only [column004Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column004Clearing column004Clearing_ne_zero _ h
theorem column004_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 4) = W (fun i => value x (basisData i)) (fun i => matrix_e i 4) := by
  have h := column004_value_zero x hWA
  rw [column004Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column004_identity
theorem column005_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column005Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column005Pairs column005Checked
  simp only [column005Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column005Clearing column005Clearing_ne_zero _ h
theorem column005_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 5) = W (fun i => value x (basisData i)) (fun i => matrix_e i 5) := by
  have h := column005_value_zero x hWA
  rw [column005Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column005_identity
theorem column006_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column006Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column006Pairs column006Checked
  simp only [column006Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column006Clearing column006Clearing_ne_zero _ h
theorem column006_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 6) = W (fun i => value x (basisData i)) (fun i => matrix_e i 6) := by
  have h := column006_value_zero x hWA
  rw [column006Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column006_identity
theorem column007_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column007Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column007Pairs column007Checked
  simp only [column007Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column007Clearing column007Clearing_ne_zero _ h
theorem column007_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 7) = W (fun i => value x (basisData i)) (fun i => matrix_e i 7) := by
  have h := column007_value_zero x hWA
  rw [column007Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column007_identity
end N6.Weighted49
