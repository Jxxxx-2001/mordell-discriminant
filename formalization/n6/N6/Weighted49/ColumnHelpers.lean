import N6.Weighted49.ColumnCore
import N6.Weighted49.SemanticsHelpers
import N6.Weighted49.LinearSemantics
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem value_polyLin {R : Type*} [CommRing R] (x : Fin 5 → R) {n : Nat} :
    ∀ (mons : Fin n → Mon) (v : Fin n → Int), value x (polyLin mons v) = W (fun i => monVal x (mons i)) v := by
  induction n with
  | zero => intro mons v; simp [polyLin, value, W]
  | succ n ih =>
    intro mons v
    rw [polyLin, value_merge, ih]
    simp only [value, add_zero, W, Fin.sum_univ_succ]
theorem W_neg {R : Type*} [CommRing R] {n : Nat} (basis : Fin n → R) (v : Fin n → Int) :
    W basis (fun i => -v i) = -W basis v := by
  simp [W, Int.cast_neg, neg_mul, Finset.sum_neg_distrib]
theorem value_columnPoly {R : Type*} [CommRing R] (x : Fin 5 → R) (m : Mon) (y : R)
    (hm : monVal x m = y) (G : Int) (j : Fin 49) (M : Fin 49 → Fin 49 → Int) :
    value x (columnPoly m G j M) = (G : R)*y*value x (basisData j) - W (fun i => value x (basisData i)) (fun i => M i j) := by
  simp only [columnPoly, value_merge, value, add_zero, value_polyLin, monVal_plus, hm, W_neg, value_basis]
  ring
theorem variableMon_value_1 {R : Type*} [CommRing R] (x : Fin 5 → R) : monVal x (variableMon 1) = x 1 := by simp [variableMon, monVal]
theorem variableMon_value_2 {R : Type*} [CommRing R] (x : Fin 5 → R) : monVal x (variableMon 2) = x 2 := by simp [variableMon, monVal]
theorem variableMon_value_3 {R : Type*} [CommRing R] (x : Fin 5 → R) : monVal x (variableMon 3) = x 3 := by simp [variableMon, monVal]
theorem variableMon_value_4 {R : Type*} [CommRing R] (x : Fin 5 → R) : monVal x (variableMon 4) = x 4 := by simp [variableMon, monVal]
#print axioms value_polyLin
#print axioms value_columnPoly
end N6.Weighted49
