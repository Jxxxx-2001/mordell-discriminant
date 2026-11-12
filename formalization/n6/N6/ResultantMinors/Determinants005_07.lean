import N6.ResultantMinors.Determinants005_06
import N6.ResultantMinors.Arithmetic005
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem cutEdge043_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut043 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut042 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols043 ((0 : Fin 4).succAbove l) = minorCols042 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge043_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut043 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut041 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols043 ((1 : Fin 4).succAbove l) = minorCols041 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge043_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut043 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut035 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols043 ((2 : Fin 4).succAbove l) = minorCols035 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge043_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut043 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut011 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols043 ((3 : Fin 4).succAbove l) = minorCols011 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet043 (b c d e U : ℂ) :
    (cut043 (presentation b c d e U 0)).det = value (point b c d e U) D043 ∧
    HasDerivAt (fun T : ℂ => (cut043 (presentation b c d e U T)).det) (value (point b c d e U) J043) 0 := by
  have he (j : Fin 4) : cut043 (presentation b c d e U 0) 0 j = entriesA043 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 5
  have he' (j : Fin 4) : HasDerivAt (fun T : ℂ => cut043 (presentation b c d e U T) 0 j)
      (entriesH043 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd (j : Fin 4) : ((cut043 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD043 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge043_0] using (detJet042 b c d e U).1
    · simpa only [cutEdge043_1] using (detJet041 b c d e U).1
    · simpa only [cutEdge043_2] using (detJet035 b c d e U).1
    · simpa only [cutEdge043_3] using (detJet011 b c d e U).1
  have hd' (j : Fin 4) : HasDerivAt (fun T : ℂ =>
      ((cut043 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ043 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge043_0] using (detJet042 b c d e U).2
    · simpa only [cutEdge043_1] using (detJet041 b c d e U).2
    · simpa only [cutEdge043_2] using (detJet035 b c d e U).2
    · simpa only [cutEdge043_3] using (detJet011 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut043 (presentation b c d e U T))
    (entriesA043 (point b c d e U)) (entriesH043 (point b c d e U)) (childD043 (point b c d e U)) (childJ043 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity043 (point b c d e U)).symm
  · rw [linear_identity043 (point b c d e U)]
    exact step.2
end N6.ResultantMinors
