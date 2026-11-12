import N6.ResultantMinors.Determinants004
import N6.ResultantMinors.Arithmetic005
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem cutEdge056_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut056 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut048 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols056 ((0 : Fin 3).succAbove l) = minorCols048 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge056_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut056 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut040 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols056 ((1 : Fin 3).succAbove l) = minorCols040 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge056_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut056 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut024 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols056 ((2 : Fin 3).succAbove l) = minorCols024 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet056 (b c d e U : ℂ) :
    (cut056 (presentation b c d e U 0)).det = value (point b c d e U) D056 ∧
    HasDerivAt (fun T : ℂ => (cut056 (presentation b c d e U T)).det) (value (point b c d e U) J056) 0 := by
  have he (j : Fin 3) : cut056 (presentation b c d e U 0) 0 j = entriesA056 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 3 3
    · exact presentation_entry_zero b c d e U 3 4
    · exact presentation_entry_zero b c d e U 3 5
  have he' (j : Fin 3) : HasDerivAt (fun T : ℂ => cut056 (presentation b c d e U T) 0 j)
      (entriesH056 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 3 3
    · exact presentation_entry_hasDerivAt b c d e U 3 4
    · exact presentation_entry_hasDerivAt b c d e U 3 5
  have hd (j : Fin 3) : ((cut056 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD056 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge056_0] using (detJet048 b c d e U).1
    · simpa only [cutEdge056_1] using (detJet040 b c d e U).1
    · simpa only [cutEdge056_2] using (detJet024 b c d e U).1
  have hd' (j : Fin 3) : HasDerivAt (fun T : ℂ =>
      ((cut056 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ056 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge056_0] using (detJet048 b c d e U).2
    · simpa only [cutEdge056_1] using (detJet040 b c d e U).2
    · simpa only [cutEdge056_2] using (detJet024 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut056 (presentation b c d e U T))
    (entriesA056 (point b c d e U)) (entriesH056 (point b c d e U)) (childD056 (point b c d e U)) (childJ056 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity056 (point b c d e U)).symm
  · rw [linear_identity056 (point b c d e U)]
    exact step.2
end N6.ResultantMinors
