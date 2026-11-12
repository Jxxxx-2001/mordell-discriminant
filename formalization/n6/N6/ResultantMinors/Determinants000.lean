import N6.ResultantMinors.DeterminantsBase
import N6.ResultantMinors.Arithmetic000
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem cutEdge001_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut001 A).submatrix Fin.succ (0 : Fin 1).succAbove = cut000 A := by
  apply Matrix.ext
  intro i l
  exact Fin.elim0 i
theorem detJet001 (b c d e U : ℂ) :
    (cut001 (presentation b c d e U 0)).det = value (point b c d e U) D001 ∧
    HasDerivAt (fun T : ℂ => (cut001 (presentation b c d e U T)).det) (value (point b c d e U) J001) 0 := by
  have he (j : Fin 1) : cut001 (presentation b c d e U 0) 0 j = entriesA001 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 5 0
  have he' (j : Fin 1) : HasDerivAt (fun T : ℂ => cut001 (presentation b c d e U T) 0 j)
      (entriesH001 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 5 0
  have hd (j : Fin 1) : ((cut001 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD001 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge001_0] using (detJet000 b c d e U).1
  have hd' (j : Fin 1) : HasDerivAt (fun T : ℂ =>
      ((cut001 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ001 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge001_0] using (detJet000 b c d e U).2
  have step := det_row_zero_jet (n := 0) (fun T : ℂ => cut001 (presentation b c d e U T))
    (entriesA001 (point b c d e U)) (entriesH001 (point b c d e U)) (childD001 (point b c d e U)) (childJ001 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity001 (point b c d e U)).symm
  · rw [linear_identity001 (point b c d e U)]
    exact step.2
private theorem cutEdge002_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut002 A).submatrix Fin.succ (0 : Fin 1).succAbove = cut000 A := by
  apply Matrix.ext
  intro i l
  exact Fin.elim0 i
theorem detJet002 (b c d e U : ℂ) :
    (cut002 (presentation b c d e U 0)).det = value (point b c d e U) D002 ∧
    HasDerivAt (fun T : ℂ => (cut002 (presentation b c d e U T)).det) (value (point b c d e U) J002) 0 := by
  have he (j : Fin 1) : cut002 (presentation b c d e U 0) 0 j = entriesA002 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 5 1
  have he' (j : Fin 1) : HasDerivAt (fun T : ℂ => cut002 (presentation b c d e U T) 0 j)
      (entriesH002 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 5 1
  have hd (j : Fin 1) : ((cut002 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD002 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge002_0] using (detJet000 b c d e U).1
  have hd' (j : Fin 1) : HasDerivAt (fun T : ℂ =>
      ((cut002 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ002 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge002_0] using (detJet000 b c d e U).2
  have step := det_row_zero_jet (n := 0) (fun T : ℂ => cut002 (presentation b c d e U T))
    (entriesA002 (point b c d e U)) (entriesH002 (point b c d e U)) (childD002 (point b c d e U)) (childJ002 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity002 (point b c d e U)).symm
  · rw [linear_identity002 (point b c d e U)]
    exact step.2
private theorem cutEdge004_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut004 A).submatrix Fin.succ (0 : Fin 1).succAbove = cut000 A := by
  apply Matrix.ext
  intro i l
  exact Fin.elim0 i
theorem detJet004 (b c d e U : ℂ) :
    (cut004 (presentation b c d e U 0)).det = value (point b c d e U) D004 ∧
    HasDerivAt (fun T : ℂ => (cut004 (presentation b c d e U T)).det) (value (point b c d e U) J004) 0 := by
  have he (j : Fin 1) : cut004 (presentation b c d e U 0) 0 j = entriesA004 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 5 2
  have he' (j : Fin 1) : HasDerivAt (fun T : ℂ => cut004 (presentation b c d e U T) 0 j)
      (entriesH004 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 5 2
  have hd (j : Fin 1) : ((cut004 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD004 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge004_0] using (detJet000 b c d e U).1
  have hd' (j : Fin 1) : HasDerivAt (fun T : ℂ =>
      ((cut004 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ004 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge004_0] using (detJet000 b c d e U).2
  have step := det_row_zero_jet (n := 0) (fun T : ℂ => cut004 (presentation b c d e U T))
    (entriesA004 (point b c d e U)) (entriesH004 (point b c d e U)) (childD004 (point b c d e U)) (childJ004 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity004 (point b c d e U)).symm
  · rw [linear_identity004 (point b c d e U)]
    exact step.2
private theorem cutEdge008_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut008 A).submatrix Fin.succ (0 : Fin 1).succAbove = cut000 A := by
  apply Matrix.ext
  intro i l
  exact Fin.elim0 i
theorem detJet008 (b c d e U : ℂ) :
    (cut008 (presentation b c d e U 0)).det = value (point b c d e U) D008 ∧
    HasDerivAt (fun T : ℂ => (cut008 (presentation b c d e U T)).det) (value (point b c d e U) J008) 0 := by
  have he (j : Fin 1) : cut008 (presentation b c d e U 0) 0 j = entriesA008 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 5 3
  have he' (j : Fin 1) : HasDerivAt (fun T : ℂ => cut008 (presentation b c d e U T) 0 j)
      (entriesH008 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 5 3
  have hd (j : Fin 1) : ((cut008 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD008 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge008_0] using (detJet000 b c d e U).1
  have hd' (j : Fin 1) : HasDerivAt (fun T : ℂ =>
      ((cut008 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ008 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge008_0] using (detJet000 b c d e U).2
  have step := det_row_zero_jet (n := 0) (fun T : ℂ => cut008 (presentation b c d e U T))
    (entriesA008 (point b c d e U)) (entriesH008 (point b c d e U)) (childD008 (point b c d e U)) (childJ008 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity008 (point b c d e U)).symm
  · rw [linear_identity008 (point b c d e U)]
    exact step.2
private theorem cutEdge016_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut016 A).submatrix Fin.succ (0 : Fin 1).succAbove = cut000 A := by
  apply Matrix.ext
  intro i l
  exact Fin.elim0 i
theorem detJet016 (b c d e U : ℂ) :
    (cut016 (presentation b c d e U 0)).det = value (point b c d e U) D016 ∧
    HasDerivAt (fun T : ℂ => (cut016 (presentation b c d e U T)).det) (value (point b c d e U) J016) 0 := by
  have he (j : Fin 1) : cut016 (presentation b c d e U 0) 0 j = entriesA016 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 5 4
  have he' (j : Fin 1) : HasDerivAt (fun T : ℂ => cut016 (presentation b c d e U T) 0 j)
      (entriesH016 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 5 4
  have hd (j : Fin 1) : ((cut016 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD016 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge016_0] using (detJet000 b c d e U).1
  have hd' (j : Fin 1) : HasDerivAt (fun T : ℂ =>
      ((cut016 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ016 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge016_0] using (detJet000 b c d e U).2
  have step := det_row_zero_jet (n := 0) (fun T : ℂ => cut016 (presentation b c d e U T))
    (entriesA016 (point b c d e U)) (entriesH016 (point b c d e U)) (childD016 (point b c d e U)) (childJ016 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity016 (point b c d e U)).symm
  · rw [linear_identity016 (point b c d e U)]
    exact step.2
private theorem cutEdge032_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut032 A).submatrix Fin.succ (0 : Fin 1).succAbove = cut000 A := by
  apply Matrix.ext
  intro i l
  exact Fin.elim0 i
theorem detJet032 (b c d e U : ℂ) :
    (cut032 (presentation b c d e U 0)).det = value (point b c d e U) D032 ∧
    HasDerivAt (fun T : ℂ => (cut032 (presentation b c d e U T)).det) (value (point b c d e U) J032) 0 := by
  have he (j : Fin 1) : cut032 (presentation b c d e U 0) 0 j = entriesA032 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 5 5
  have he' (j : Fin 1) : HasDerivAt (fun T : ℂ => cut032 (presentation b c d e U T) 0 j)
      (entriesH032 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 5 5
  have hd (j : Fin 1) : ((cut032 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD032 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge032_0] using (detJet000 b c d e U).1
  have hd' (j : Fin 1) : HasDerivAt (fun T : ℂ =>
      ((cut032 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ032 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge032_0] using (detJet000 b c d e U).2
  have step := det_row_zero_jet (n := 0) (fun T : ℂ => cut032 (presentation b c d e U T))
    (entriesA032 (point b c d e U)) (entriesH032 (point b c d e U)) (childD032 (point b c d e U)) (childJ032 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity032 (point b c d e U)).symm
  · rw [linear_identity032 (point b c d e U)]
    exact step.2
private theorem cutEdge003_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut003 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut002 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols003 ((0 : Fin 2).succAbove l) = minorCols002 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge003_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut003 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut001 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols003 ((1 : Fin 2).succAbove l) = minorCols001 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet003 (b c d e U : ℂ) :
    (cut003 (presentation b c d e U 0)).det = value (point b c d e U) D003 ∧
    HasDerivAt (fun T : ℂ => (cut003 (presentation b c d e U T)).det) (value (point b c d e U) J003) 0 := by
  have he (j : Fin 2) : cut003 (presentation b c d e U 0) 0 j = entriesA003 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 4 0
    · exact presentation_entry_zero b c d e U 4 1
  have he' (j : Fin 2) : HasDerivAt (fun T : ℂ => cut003 (presentation b c d e U T) 0 j)
      (entriesH003 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 4 0
    · exact presentation_entry_hasDerivAt b c d e U 4 1
  have hd (j : Fin 2) : ((cut003 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD003 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge003_0] using (detJet002 b c d e U).1
    · simpa only [cutEdge003_1] using (detJet001 b c d e U).1
  have hd' (j : Fin 2) : HasDerivAt (fun T : ℂ =>
      ((cut003 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ003 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge003_0] using (detJet002 b c d e U).2
    · simpa only [cutEdge003_1] using (detJet001 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut003 (presentation b c d e U T))
    (entriesA003 (point b c d e U)) (entriesH003 (point b c d e U)) (childD003 (point b c d e U)) (childJ003 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity003 (point b c d e U)).symm
  · rw [linear_identity003 (point b c d e U)]
    exact step.2
private theorem cutEdge005_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut005 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut004 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols005 ((0 : Fin 2).succAbove l) = minorCols004 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge005_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut005 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut001 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols005 ((1 : Fin 2).succAbove l) = minorCols001 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet005 (b c d e U : ℂ) :
    (cut005 (presentation b c d e U 0)).det = value (point b c d e U) D005 ∧
    HasDerivAt (fun T : ℂ => (cut005 (presentation b c d e U T)).det) (value (point b c d e U) J005) 0 := by
  have he (j : Fin 2) : cut005 (presentation b c d e U 0) 0 j = entriesA005 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 4 0
    · exact presentation_entry_zero b c d e U 4 2
  have he' (j : Fin 2) : HasDerivAt (fun T : ℂ => cut005 (presentation b c d e U T) 0 j)
      (entriesH005 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 4 0
    · exact presentation_entry_hasDerivAt b c d e U 4 2
  have hd (j : Fin 2) : ((cut005 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD005 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge005_0] using (detJet004 b c d e U).1
    · simpa only [cutEdge005_1] using (detJet001 b c d e U).1
  have hd' (j : Fin 2) : HasDerivAt (fun T : ℂ =>
      ((cut005 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ005 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge005_0] using (detJet004 b c d e U).2
    · simpa only [cutEdge005_1] using (detJet001 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut005 (presentation b c d e U T))
    (entriesA005 (point b c d e U)) (entriesH005 (point b c d e U)) (childD005 (point b c d e U)) (childJ005 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity005 (point b c d e U)).symm
  · rw [linear_identity005 (point b c d e U)]
    exact step.2
end N6.ResultantMinors
