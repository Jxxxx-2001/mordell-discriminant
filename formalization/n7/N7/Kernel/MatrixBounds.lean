import N7.Kernel.MatrixCheckData
set_option autoImplicit false
set_option maxRecDepth 64000
set_option maxHeartbeats 0
namespace N7.Kernel
open Checks

theorem matrix_log2_checked : logCheck 2 log2Interval.lo log2Interval.hi 40 = true := by
  decide +kernel

theorem matrix_log3_checked : logCheck 3 log3Interval.lo log3Interval.hi 40 = true := by
  decide +kernel

theorem matrix_log2_contains : log2Interval.Contains (Real.log 2) := by
  simpa [QInterval.Contains] using
    logCheck_sound 2 log2Interval.lo log2Interval.hi 40 matrix_log2_checked

theorem matrix_log3_contains : log3Interval.Contains (Real.log 3) := by
  simpa [QInterval.Contains] using
    logCheck_sound 3 log3Interval.lo log3Interval.hi 40 matrix_log3_checked

theorem matrix_error_checked : ∀ k i j, (matrixEntryError k i j).norm ≤ matrixError := by
  decide +kernel

theorem matrix_symmetry_checked : ∀ k i j,
    matrixA k i j = matrixA k j i ∧ matrixB k i j = matrixB k j i ∧
      matrixC k i j = matrixC k j i := by
  decide +kernel

theorem matrix_isHermitian (k : Fin 6) : (matrix k).IsHermitian := by
  change (matrix k).conjTranspose = matrix k
  ext i j
  simp only [Matrix.conjTranspose_apply, star_trivial, matrix]
  obtain ⟨ha, hb, hc⟩ := matrix_symmetry_checked k j i
  rw [ha, hb, hc]

theorem matrix_entry_error_bound (k : Fin 6) (i j : Fin 4) :
    |matrix k i j - realMatrix (matrixCenter k) i j| ≤ (matrixError : ℝ) := by
  have h0 : (⟨matrixA k i j - matrixCenter k i j,
      matrixA k i j - matrixCenter k i j⟩ : QInterval).Contains
      ((matrixA k i j : ℝ) - (matrixCenter k i j : ℝ)) := by
    simp [QInterval.Contains]
  have h1 := QInterval.add_sound h0
    (QInterval.scale_sound (matrixB k i j) matrix_log2_contains)
  have h2 := QInterval.add_sound h1
    (QInterval.scale_sound (matrixC k i j) matrix_log3_contains)
  have hc : (matrixEntryError k i j).Contains
      (matrix k i j - realMatrix (matrixCenter k) i j) := by
    convert h2 using 1 <;> simp [matrixEntryError, matrix, realMatrix] <;> ring
  apply (QInterval.norm_sound hc).trans
  exact_mod_cast matrix_error_checked k i j

#print axioms matrix_entry_error_bound
#print axioms matrix_isHermitian
end N7.Kernel
