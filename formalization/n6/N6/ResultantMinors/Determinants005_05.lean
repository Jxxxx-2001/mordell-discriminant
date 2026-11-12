import N6.ResultantMinors.Determinants005_04
import N6.ResultantMinors.Arithmetic005
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem cutEdge030_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut030 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut028 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols030 ((0 : Fin 4).succAbove l) = minorCols028 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge030_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut030 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut026 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols030 ((1 : Fin 4).succAbove l) = minorCols026 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge030_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut030 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut022 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols030 ((2 : Fin 4).succAbove l) = minorCols022 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge030_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut030 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut014 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows4 i.succ = suffixRows3 i := by fin_cases i <;> rfl
  have hc : minorCols030 ((3 : Fin 4).succAbove l) = minorCols014 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet030 (b c d e U : ℂ) :
    (cut030 (presentation b c d e U 0)).det = value (point b c d e U) D030 ∧
    HasDerivAt (fun T : ℂ => (cut030 (presentation b c d e U T)).det) (value (point b c d e U) J030) 0 := by
  have he (j : Fin 4) : cut030 (presentation b c d e U 0) 0 j = entriesA030 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 4
  have he' (j : Fin 4) : HasDerivAt (fun T : ℂ => cut030 (presentation b c d e U T) 0 j)
      (entriesH030 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 4
  have hd (j : Fin 4) : ((cut030 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD030 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge030_0] using (detJet028 b c d e U).1
    · simpa only [cutEdge030_1] using (detJet026 b c d e U).1
    · simpa only [cutEdge030_2] using (detJet022 b c d e U).1
    · simpa only [cutEdge030_3] using (detJet014 b c d e U).1
  have hd' (j : Fin 4) : HasDerivAt (fun T : ℂ =>
      ((cut030 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ030 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge030_0] using (detJet028 b c d e U).2
    · simpa only [cutEdge030_1] using (detJet026 b c d e U).2
    · simpa only [cutEdge030_2] using (detJet022 b c d e U).2
    · simpa only [cutEdge030_3] using (detJet014 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut030 (presentation b c d e U T))
    (entriesA030 (point b c d e U)) (entriesH030 (point b c d e U)) (childD030 (point b c d e U)) (childJ030 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity030 (point b c d e U)).symm
  · rw [linear_identity030 (point b c d e U)]
    exact step.2
end N6.ResultantMinors
