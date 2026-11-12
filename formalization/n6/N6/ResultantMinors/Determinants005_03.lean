import N6.ResultantMinors.Determinants005_02
import N6.ResultantMinors.Arithmetic005
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem cutEdge027_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut027 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut026 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols027 ((0 : Fin 4).succAbove l) = minorCols026 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge027_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut027 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut025 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols027 ((1 : Fin 4).succAbove l) = minorCols025 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge027_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut027 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut019 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols027 ((2 : Fin 4).succAbove l) = minorCols019 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge027_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut027 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut011 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols027 ((3 : Fin 4).succAbove l) = minorCols011 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet027 (b c d e U : ℂ) :
    (cut027 (presentation b c d e U 0)).det = value (point b c d e U) D027 ∧
    HasDerivAt (fun T : ℂ => (cut027 (presentation b c d e U T)).det) (value (point b c d e U) J027) 0 := by
  have he (j : Fin 4) : cut027 (presentation b c d e U 0) 0 j = entriesA027 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 4
  have he' (j : Fin 4) : HasDerivAt (fun T : ℂ => cut027 (presentation b c d e U T) 0 j)
      (entriesH027 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 4
  have hd (j : Fin 4) : ((cut027 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD027 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge027_0] using (detJet026 b c d e U).1
    · simpa only [cutEdge027_1] using (detJet025 b c d e U).1
    · simpa only [cutEdge027_2] using (detJet019 b c d e U).1
    · simpa only [cutEdge027_3] using (detJet011 b c d e U).1
  have hd' (j : Fin 4) : HasDerivAt (fun T : ℂ =>
      ((cut027 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ027 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge027_0] using (detJet026 b c d e U).2
    · simpa only [cutEdge027_1] using (detJet025 b c d e U).2
    · simpa only [cutEdge027_2] using (detJet019 b c d e U).2
    · simpa only [cutEdge027_3] using (detJet011 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut027 (presentation b c d e U T))
    (entriesA027 (point b c d e U)) (entriesH027 (point b c d e U)) (childD027 (point b c d e U)) (childJ027 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity027 (point b c d e U)).symm
  · rw [linear_identity027 (point b c d e U)]
    exact step.2
end N6.ResultantMinors
