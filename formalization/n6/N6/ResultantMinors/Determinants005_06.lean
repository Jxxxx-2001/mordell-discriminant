import N6.ResultantMinors.Determinants005_05
import N6.ResultantMinors.Arithmetic005
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem cutEdge039_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut039 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut038 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols039 ((0 : Fin 4).succAbove l) = minorCols038 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge039_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut039 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut037 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols039 ((1 : Fin 4).succAbove l) = minorCols037 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge039_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut039 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut035 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols039 ((2 : Fin 4).succAbove l) = minorCols035 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge039_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut039 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut007 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols039 ((3 : Fin 4).succAbove l) = minorCols007 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet039 (b c d e U : ℂ) :
    (cut039 (presentation b c d e U 0)).det = value (point b c d e U) D039 ∧
    HasDerivAt (fun T : ℂ => (cut039 (presentation b c d e U T)).det) (value (point b c d e U) J039) 0 := by
  have he (j : Fin 4) : cut039 (presentation b c d e U 0) 0 j = entriesA039 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 5
  have he' (j : Fin 4) : HasDerivAt (fun T : ℂ => cut039 (presentation b c d e U T) 0 j)
      (entriesH039 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd (j : Fin 4) : ((cut039 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD039 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge039_0] using (detJet038 b c d e U).1
    · simpa only [cutEdge039_1] using (detJet037 b c d e U).1
    · simpa only [cutEdge039_2] using (detJet035 b c d e U).1
    · simpa only [cutEdge039_3] using (detJet007 b c d e U).1
  have hd' (j : Fin 4) : HasDerivAt (fun T : ℂ =>
      ((cut039 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ039 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge039_0] using (detJet038 b c d e U).2
    · simpa only [cutEdge039_1] using (detJet037 b c d e U).2
    · simpa only [cutEdge039_2] using (detJet035 b c d e U).2
    · simpa only [cutEdge039_3] using (detJet007 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut039 (presentation b c d e U T))
    (entriesA039 (point b c d e U)) (entriesH039 (point b c d e U)) (childD039 (point b c d e U)) (childJ039 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity039 (point b c d e U)).symm
  · rw [linear_identity039 (point b c d e U)]
    exact step.2
end N6.ResultantMinors
