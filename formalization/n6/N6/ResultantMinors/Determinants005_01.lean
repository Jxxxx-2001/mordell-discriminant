import N6.ResultantMinors.Determinants005_00
import N6.ResultantMinors.Arithmetic005
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem cutEdge015_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut015 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut014 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols015 ((0 : Fin 4).succAbove l) = minorCols014 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge015_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut015 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut013 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols015 ((1 : Fin 4).succAbove l) = minorCols013 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge015_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut015 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut011 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols015 ((2 : Fin 4).succAbove l) = minorCols011 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge015_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut015 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut007 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols015 ((3 : Fin 4).succAbove l) = minorCols007 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet015 (b c d e U : ℂ) :
    (cut015 (presentation b c d e U 0)).det = value (point b c d e U) D015 ∧
    HasDerivAt (fun T : ℂ => (cut015 (presentation b c d e U T)).det) (value (point b c d e U) J015) 0 := by
  have he (j : Fin 4) : cut015 (presentation b c d e U 0) 0 j = entriesA015 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 3
  have he' (j : Fin 4) : HasDerivAt (fun T : ℂ => cut015 (presentation b c d e U T) 0 j)
      (entriesH015 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 3
  have hd (j : Fin 4) : ((cut015 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD015 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge015_0] using (detJet014 b c d e U).1
    · simpa only [cutEdge015_1] using (detJet013 b c d e U).1
    · simpa only [cutEdge015_2] using (detJet011 b c d e U).1
    · simpa only [cutEdge015_3] using (detJet007 b c d e U).1
  have hd' (j : Fin 4) : HasDerivAt (fun T : ℂ =>
      ((cut015 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ015 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge015_0] using (detJet014 b c d e U).2
    · simpa only [cutEdge015_1] using (detJet013 b c d e U).2
    · simpa only [cutEdge015_2] using (detJet011 b c d e U).2
    · simpa only [cutEdge015_3] using (detJet007 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut015 (presentation b c d e U T))
    (entriesA015 (point b c d e U)) (entriesH015 (point b c d e U)) (childD015 (point b c d e U)) (childJ015 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity015 (point b c d e U)).symm
  · rw [linear_identity015 (point b c d e U)]
    exact step.2
end N6.ResultantMinors
