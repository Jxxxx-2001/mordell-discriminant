import N6.Weighted49.ColumnGround021
import N6.Weighted49.ColumnHelpers
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem column168_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column168Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column168Pairs column168Checked
  simp only [column168Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column168Clearing column168Clearing_ne_zero _ h
theorem column168_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 21) = W (fun i => value x (basisData i)) (fun i => matrix_B i 21) := by
  have h := column168_value_zero x hWA
  rw [column168Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column168_identity
theorem column169_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column169Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column169Pairs column169Checked
  simp only [column169Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column169Clearing column169Clearing_ne_zero _ h
theorem column169_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 22) = W (fun i => value x (basisData i)) (fun i => matrix_B i 22) := by
  have h := column169_value_zero x hWA
  rw [column169Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column169_identity
theorem column170_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column170Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column170Pairs column170Checked
  simp only [column170Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column170Clearing column170Clearing_ne_zero _ h
theorem column170_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 23) = W (fun i => value x (basisData i)) (fun i => matrix_B i 23) := by
  have h := column170_value_zero x hWA
  rw [column170Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column170_identity
theorem column171_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column171Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column171Pairs column171Checked
  simp only [column171Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column171Clearing column171Clearing_ne_zero _ h
theorem column171_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 24) = W (fun i => value x (basisData i)) (fun i => matrix_B i 24) := by
  have h := column171_value_zero x hWA
  rw [column171Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column171_identity
theorem column172_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column172Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column172Pairs column172Checked
  have hw : value x WA002 = 0 := by simpa only [actionData] using hWA 2
  simp only [column172Pairs, pairs, value_scalar, hw, mul_zero, add_zero] at h
  exact N6.Certificate.int_scaled_zero column172Clearing column172Clearing_ne_zero _ h
theorem column172_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 25) = W (fun i => value x (basisData i)) (fun i => matrix_B i 25) := by
  have h := column172_value_zero x hWA
  rw [column172Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column172_identity
theorem column173_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column173Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column173Pairs column173Checked
  simp only [column173Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column173Clearing column173Clearing_ne_zero _ h
theorem column173_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 26) = W (fun i => value x (basisData i)) (fun i => matrix_B i 26) := by
  have h := column173_value_zero x hWA
  rw [column173Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column173_identity
theorem column174_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column174Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column174Pairs column174Checked
  simp only [column174Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column174Clearing column174Clearing_ne_zero _ h
theorem column174_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 27) = W (fun i => value x (basisData i)) (fun i => matrix_B i 27) := by
  have h := column174_value_zero x hWA
  rw [column174Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column174_identity
theorem column175_value_zero {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    value x column175Poly = 0 := by
  have h := N6.SparseProductReduce.pairs_vanish x column175Pairs column175Checked
  simp only [column175Pairs, pairs, value_scalar, add_zero] at h
  exact N6.Certificate.int_scaled_zero column175Clearing column175Clearing_ne_zero _ h
theorem column175_identity {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0) :
    (matrix_BDen : R) * x 4 * value x (basisData 28) = W (fun i => value x (basisData i)) (fun i => matrix_B i 28) := by
  have h := column175_value_zero x hWA
  rw [column175Poly, value_columnPoly x _ _ (variableMon_value_4 x)] at h
  exact sub_eq_zero.mp h
#print axioms column175_identity
end N6.Weighted49
