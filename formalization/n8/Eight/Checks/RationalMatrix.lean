-- Snapshot of the general n9-project tool; namespace isolated for n8.
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Rat.Cast.Order
import Mathlib.Data.Real.StarOrdered
import Mathlib.Tactic

namespace MordellEight.Checks
open Matrix

def realMatrix {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) : Matrix (Fin n) (Fin n) ℝ :=
  fun i j => (A i j : ℝ)

theorem realMatrix_mul {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℚ) :
    realMatrix (A * B) = realMatrix A * realMatrix B := by
  ext i j
  simp [realMatrix, Matrix.mul_apply]

theorem realMatrix_transpose {n : ℕ} (A : Matrix (Fin n) (Fin n) ℚ) :
    realMatrix A.transpose = (realMatrix A).transpose := rfl

theorem realMatrix_diagonal {n : ℕ} (d : Fin n → ℚ) :
    realMatrix (Matrix.diagonal d) = Matrix.diagonal (fun i => (d i : ℝ)) := by
  ext i j
  by_cases h : i = j <;> simp [realMatrix, h]

theorem realMatrix_one {n : ℕ} :
    realMatrix (1 : Matrix (Fin n) (Fin n) ℚ) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [realMatrix, Matrix.one_apply, h]

/-- The external program supplies U, R and d. The checker verifies every equality over ℚ. -/
def factorCheck {n : ℕ} (A U R : Matrix (Fin n) (Fin n) ℚ) (d : Fin n → ℚ) : Bool :=
  decide (U.transpose * Matrix.diagonal d * U = A ∧ R * U = 1 ∧ ∀ i, 0 < d i)

theorem factorCheck_sound {n : ℕ} (A U R : Matrix (Fin n) (Fin n) ℚ)
    (d : Fin n → ℚ) (h : factorCheck A U R d = true) : (realMatrix A).PosDef := by
  have hc : U.transpose * Matrix.diagonal d * U = A ∧ R * U = 1 ∧ ∀ i, 0 < d i :=
    of_decide_eq_true h
  have hmul : realMatrix R * realMatrix U = 1 := by
    have hh := congrArg realMatrix hc.2.1
    simpa only [realMatrix_mul, realMatrix_one] using hh
  have hinj : Function.Injective (realMatrix U).mulVec := by
    intro x y hxy
    have hh := congrArg (fun v => realMatrix R *ᵥ v) hxy
    simpa only [Matrix.mulVec_mulVec, hmul, Matrix.one_mulVec] using hh
  have hd : (Matrix.diagonal (fun i => (d i : ℝ))).PosDef := by
    apply Matrix.posDef_diagonal_iff.mpr
    intro i
    exact_mod_cast hc.2.2 i
  have hp := hd.conjTranspose_mul_mul_same hinj
  have heq := congrArg realMatrix hc.1
  rw [realMatrix_mul, realMatrix_mul, realMatrix_transpose, realMatrix_diagonal] at heq
  simpa only [Matrix.conjTranspose_eq_transpose_of_trivial, heq] using hp

end MordellEight.Checks
