import N6.ResultantMinors.Determinants005_01
import N6.ResultantMinors.Arithmetic005
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem cutEdge023_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut023 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut022 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols023 ((0 : Fin 4).succAbove l) = minorCols022 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge023_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut023 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut021 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols023 ((1 : Fin 4).succAbove l) = minorCols021 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge023_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut023 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut019 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols023 ((2 : Fin 4).succAbove l) = minorCols019 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge023_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut023 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut007 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols023 ((3 : Fin 4).succAbove l) = minorCols007 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet023 (b c d e U : ℂ) :
    (cut023 (presentation b c d e U 0)).det = value (point b c d e U) D023 ∧
    HasDerivAt (fun T : ℂ => (cut023 (presentation b c d e U T)).det) (value (point b c d e U) J023) 0 := by
  have he (j : Fin 4) : cut023 (presentation b c d e U 0) 0 j = entriesA023 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 4
  have he' (j : Fin 4) : HasDerivAt (fun T : ℂ => cut023 (presentation b c d e U T) 0 j)
      (entriesH023 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 4
  have hd (j : Fin 4) : ((cut023 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD023 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge023_0] using (detJet022 b c d e U).1
    · simpa only [cutEdge023_1] using (detJet021 b c d e U).1
    · simpa only [cutEdge023_2] using (detJet019 b c d e U).1
    · simpa only [cutEdge023_3] using (detJet007 b c d e U).1
  have hd' (j : Fin 4) : HasDerivAt (fun T : ℂ =>
      ((cut023 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ023 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge023_0] using (detJet022 b c d e U).2
    · simpa only [cutEdge023_1] using (detJet021 b c d e U).2
    · simpa only [cutEdge023_2] using (detJet019 b c d e U).2
    · simpa only [cutEdge023_3] using (detJet007 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut023 (presentation b c d e U T))
    (entriesA023 (point b c d e U)) (entriesH023 (point b c d e U)) (childD023 (point b c d e U)) (childJ023 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity023 (point b c d e U)).symm
  · rw [linear_identity023 (point b c d e U)]
    exact step.2
end N6.ResultantMinors
