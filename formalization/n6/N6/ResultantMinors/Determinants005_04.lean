import N6.ResultantMinors.Determinants005_03
import N6.ResultantMinors.Arithmetic005
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem cutEdge029_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut029 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut028 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols029 ((0 : Fin 4).succAbove l) = minorCols028 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge029_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut029 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut025 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols029 ((1 : Fin 4).succAbove l) = minorCols025 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge029_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut029 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut021 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols029 ((2 : Fin 4).succAbove l) = minorCols021 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge029_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut029 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut013 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols029 ((3 : Fin 4).succAbove l) = minorCols013 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet029 (b c d e U : ℂ) :
    (cut029 (presentation b c d e U 0)).det = value (point b c d e U) D029 ∧
    HasDerivAt (fun T : ℂ => (cut029 (presentation b c d e U T)).det) (value (point b c d e U) J029) 0 := by
  have he (j : Fin 4) : cut029 (presentation b c d e U 0) 0 j = entriesA029 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 4
  have he' (j : Fin 4) : HasDerivAt (fun T : ℂ => cut029 (presentation b c d e U T) 0 j)
      (entriesH029 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 4
  have hd (j : Fin 4) : ((cut029 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD029 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge029_0] using (detJet028 b c d e U).1
    · simpa only [cutEdge029_1] using (detJet025 b c d e U).1
    · simpa only [cutEdge029_2] using (detJet021 b c d e U).1
    · simpa only [cutEdge029_3] using (detJet013 b c d e U).1
  have hd' (j : Fin 4) : HasDerivAt (fun T : ℂ =>
      ((cut029 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ029 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge029_0] using (detJet028 b c d e U).2
    · simpa only [cutEdge029_1] using (detJet025 b c d e U).2
    · simpa only [cutEdge029_2] using (detJet021 b c d e U).2
    · simpa only [cutEdge029_3] using (detJet013 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut029 (presentation b c d e U T))
    (entriesA029 (point b c d e U)) (entriesH029 (point b c d e U)) (childD029 (point b c d e U)) (childJ029 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity029 (point b c d e U)).symm
  · rw [linear_identity029 (point b c d e U)]
    exact step.2
end N6.ResultantMinors
