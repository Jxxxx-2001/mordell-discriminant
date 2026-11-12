import N6.Weighted49.ColumnGround001
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column008_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column008Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column008Pairs column008Checked
  simp only [column008Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column008Clearing column008Clearing_ne_zero _ h
theorem column008_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 8) = W (fun i => value x (basisData i)) (fun i => matrix_e i 8) := by
  have h := column008_value_zero x hWA
  rw [column008Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column008_identity
theorem column009_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column009Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column009Pairs column009Checked
  simp only [column009Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column009Clearing column009Clearing_ne_zero _ h
theorem column009_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 9) = W (fun i => value x (basisData i)) (fun i => matrix_e i 9) := by
  have h := column009_value_zero x hWA
  rw [column009Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column009_identity
theorem column010_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column010Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column010Pairs column010Checked
  simp only [column010Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column010Clearing column010Clearing_ne_zero _ h
theorem column010_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 10) = W (fun i => value x (basisData i)) (fun i => matrix_e i 10) := by
  have h := column010_value_zero x hWA
  rw [column010Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column010_identity
theorem column011_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column011Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column011Pairs column011Checked
  simp only [column011Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column011Clearing column011Clearing_ne_zero _ h
theorem column011_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 11) = W (fun i => value x (basisData i)) (fun i => matrix_e i 11) := by
  have h := column011_value_zero x hWA
  rw [column011Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column011_identity
theorem column012_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column012Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column012Pairs column012Checked
  simp only [column012Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column012Clearing column012Clearing_ne_zero _ h
theorem column012_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 12) = W (fun i => value x (basisData i)) (fun i => matrix_e i 12) := by
  have h := column012_value_zero x hWA
  rw [column012Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column012_identity
theorem column013_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column013Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column013Pairs column013Checked
  simp only [column013Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column013Clearing column013Clearing_ne_zero _ h
theorem column013_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 13) = W (fun i => value x (basisData i)) (fun i => matrix_e i 13) := by
  have h := column013_value_zero x hWA
  rw [column013Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column013_identity
theorem column014_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column014Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column014Pairs column014Checked
  simp only [column014Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column014Clearing column014Clearing_ne_zero _ h
theorem column014_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 14) = W (fun i => value x (basisData i)) (fun i => matrix_e i 14) := by
  have h := column014_value_zero x hWA
  rw [column014Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column014_identity
theorem column015_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column015Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column015Pairs column015Checked
  have hw : value x WA020 = 0 := by simpa only [actionData] using hWA 20
  simp only [column015Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column015Clearing column015Clearing_ne_zero _ h
theorem column015_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_eDen : R) * x 1 * value x (basisData 15) = W (fun i => value x (basisData i)) (fun i => matrix_e i 15) := by
  have h := column015_value_zero x hWA
  rw [column015Poly, value_columnPoly x _ _ (variableMon_value_1 x)] at h
  exact sub_eq_zero.mp h
#print axioms column015_identity
end N6.Weighted49
