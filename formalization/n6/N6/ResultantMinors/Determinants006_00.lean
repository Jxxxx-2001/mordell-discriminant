import N6.ResultantMinors.Determinants005_07
import N6.ResultantMinors.Arithmetic006
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem cutEdge045_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut045 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut044 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols045 ((0 : Fin 4).succAbove l) = minorCols044 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge045_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut045 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut041 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols045 ((1 : Fin 4).succAbove l) = minorCols041 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge045_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut045 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut037 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols045 ((2 : Fin 4).succAbove l) = minorCols037 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge045_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut045 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut013 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols045 ((3 : Fin 4).succAbove l) = minorCols013 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet045 (b c d e U : ℂ) :
    (cut045 (presentation b c d e U 0)).det = value (point b c d e U) D045 ∧
    HasDerivAt (fun T : ℂ => (cut045 (presentation b c d e U T)).det) (value (point b c d e U) J045) 0 := by
  have he (j : Fin 4) : cut045 (presentation b c d e U 0) 0 j = entriesA045 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 5
  have he' (j : Fin 4) : HasDerivAt (fun T : ℂ => cut045 (presentation b c d e U T) 0 j)
      (entriesH045 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd (j : Fin 4) : ((cut045 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD045 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge045_0] using (detJet044 b c d e U).1
    · simpa only [cutEdge045_1] using (detJet041 b c d e U).1
    · simpa only [cutEdge045_2] using (detJet037 b c d e U).1
    · simpa only [cutEdge045_3] using (detJet013 b c d e U).1
  have hd' (j : Fin 4) : HasDerivAt (fun T : ℂ =>
      ((cut045 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ045 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge045_0] using (detJet044 b c d e U).2
    · simpa only [cutEdge045_1] using (detJet041 b c d e U).2
    · simpa only [cutEdge045_2] using (detJet037 b c d e U).2
    · simpa only [cutEdge045_3] using (detJet013 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut045 (presentation b c d e U T))
    (entriesA045 (point b c d e U)) (entriesH045 (point b c d e U)) (childD045 (point b c d e U)) (childJ045 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity045 (point b c d e U)).symm
  · rw [linear_identity045 (point b c d e U)]
    exact step.2
end N6.ResultantMinors
