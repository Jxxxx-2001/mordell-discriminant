import N6.ResultantMinors.Determinants006_00
import N6.ResultantMinors.Arithmetic006
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem cutEdge046_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut046 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut044 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols046 ((0 : Fin 4).succAbove l) = minorCols044 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge046_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut046 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut042 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols046 ((1 : Fin 4).succAbove l) = minorCols042 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge046_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut046 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut038 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols046 ((2 : Fin 4).succAbove l) = minorCols038 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge046_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut046 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut014 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols046 ((3 : Fin 4).succAbove l) = minorCols014 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet046 (b c d e U : ℂ) :
    (cut046 (presentation b c d e U 0)).det = value (point b c d e U) D046 ∧
    HasDerivAt (fun T : ℂ => (cut046 (presentation b c d e U T)).det) (value (point b c d e U) J046) 0 := by
  have he (j : Fin 4) : cut046 (presentation b c d e U 0) 0 j = entriesA046 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 5
  have he' (j : Fin 4) : HasDerivAt (fun T : ℂ => cut046 (presentation b c d e U T) 0 j)
      (entriesH046 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd (j : Fin 4) : ((cut046 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD046 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge046_0] using (detJet044 b c d e U).1
    · simpa only [cutEdge046_1] using (detJet042 b c d e U).1
    · simpa only [cutEdge046_2] using (detJet038 b c d e U).1
    · simpa only [cutEdge046_3] using (detJet014 b c d e U).1
  have hd' (j : Fin 4) : HasDerivAt (fun T : ℂ =>
      ((cut046 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ046 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge046_0] using (detJet044 b c d e U).2
    · simpa only [cutEdge046_1] using (detJet042 b c d e U).2
    · simpa only [cutEdge046_2] using (detJet038 b c d e U).2
    · simpa only [cutEdge046_3] using (detJet014 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut046 (presentation b c d e U T))
    (entriesA046 (point b c d e U)) (entriesH046 (point b c d e U)) (childD046 (point b c d e U)) (childJ046 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity046 (point b c d e U)).symm
  · rw [linear_identity046 (point b c d e U)]
    exact step.2
end N6.ResultantMinors
