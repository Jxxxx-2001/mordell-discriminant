import N6.ResultantMinors.Determinants001
import N6.ResultantMinors.Arithmetic002
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem cutEdge033_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut033 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut032 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols033 ((0 : Fin 2).succAbove l) = minorCols032 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge033_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut033 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut001 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols033 ((1 : Fin 2).succAbove l) = minorCols001 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet033 (b c d e U : ℂ) :
    (cut033 (presentation b c d e U 0)).det = value (point b c d e U) D033 ∧
    HasDerivAt (fun T : ℂ => (cut033 (presentation b c d e U T)).det) (value (point b c d e U) J033) 0 := by
  have he (j : Fin 2) : cut033 (presentation b c d e U 0) 0 j = entriesA033 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 4 0
    · exact presentation_entry_zero b c d e U 4 5
  have he' (j : Fin 2) : HasDerivAt (fun T : ℂ => cut033 (presentation b c d e U T) 0 j)
      (entriesH033 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 4 0
    · exact presentation_entry_hasDerivAt b c d e U 4 5
  have hd (j : Fin 2) : ((cut033 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD033 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge033_0] using (detJet032 b c d e U).1
    · simpa only [cutEdge033_1] using (detJet001 b c d e U).1
  have hd' (j : Fin 2) : HasDerivAt (fun T : ℂ =>
      ((cut033 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ033 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge033_0] using (detJet032 b c d e U).2
    · simpa only [cutEdge033_1] using (detJet001 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut033 (presentation b c d e U T))
    (entriesA033 (point b c d e U)) (entriesH033 (point b c d e U)) (childD033 (point b c d e U)) (childJ033 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity033 (point b c d e U)).symm
  · rw [linear_identity033 (point b c d e U)]
    exact step.2
private theorem cutEdge034_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut034 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut032 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols034 ((0 : Fin 2).succAbove l) = minorCols032 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge034_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut034 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut002 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols034 ((1 : Fin 2).succAbove l) = minorCols002 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet034 (b c d e U : ℂ) :
    (cut034 (presentation b c d e U 0)).det = value (point b c d e U) D034 ∧
    HasDerivAt (fun T : ℂ => (cut034 (presentation b c d e U T)).det) (value (point b c d e U) J034) 0 := by
  have he (j : Fin 2) : cut034 (presentation b c d e U 0) 0 j = entriesA034 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 4 1
    · exact presentation_entry_zero b c d e U 4 5
  have he' (j : Fin 2) : HasDerivAt (fun T : ℂ => cut034 (presentation b c d e U T) 0 j)
      (entriesH034 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 4 1
    · exact presentation_entry_hasDerivAt b c d e U 4 5
  have hd (j : Fin 2) : ((cut034 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD034 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge034_0] using (detJet032 b c d e U).1
    · simpa only [cutEdge034_1] using (detJet002 b c d e U).1
  have hd' (j : Fin 2) : HasDerivAt (fun T : ℂ =>
      ((cut034 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ034 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge034_0] using (detJet032 b c d e U).2
    · simpa only [cutEdge034_1] using (detJet002 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut034 (presentation b c d e U T))
    (entriesA034 (point b c d e U)) (entriesH034 (point b c d e U)) (childD034 (point b c d e U)) (childJ034 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity034 (point b c d e U)).symm
  · rw [linear_identity034 (point b c d e U)]
    exact step.2
private theorem cutEdge036_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut036 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut032 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols036 ((0 : Fin 2).succAbove l) = minorCols032 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge036_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut036 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut004 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols036 ((1 : Fin 2).succAbove l) = minorCols004 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet036 (b c d e U : ℂ) :
    (cut036 (presentation b c d e U 0)).det = value (point b c d e U) D036 ∧
    HasDerivAt (fun T : ℂ => (cut036 (presentation b c d e U T)).det) (value (point b c d e U) J036) 0 := by
  have he (j : Fin 2) : cut036 (presentation b c d e U 0) 0 j = entriesA036 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 4 2
    · exact presentation_entry_zero b c d e U 4 5
  have he' (j : Fin 2) : HasDerivAt (fun T : ℂ => cut036 (presentation b c d e U T) 0 j)
      (entriesH036 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 4 2
    · exact presentation_entry_hasDerivAt b c d e U 4 5
  have hd (j : Fin 2) : ((cut036 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD036 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge036_0] using (detJet032 b c d e U).1
    · simpa only [cutEdge036_1] using (detJet004 b c d e U).1
  have hd' (j : Fin 2) : HasDerivAt (fun T : ℂ =>
      ((cut036 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ036 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge036_0] using (detJet032 b c d e U).2
    · simpa only [cutEdge036_1] using (detJet004 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut036 (presentation b c d e U T))
    (entriesA036 (point b c d e U)) (entriesH036 (point b c d e U)) (childD036 (point b c d e U)) (childJ036 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity036 (point b c d e U)).symm
  · rw [linear_identity036 (point b c d e U)]
    exact step.2
private theorem cutEdge040_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut040 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut032 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols040 ((0 : Fin 2).succAbove l) = minorCols032 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge040_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut040 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut008 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols040 ((1 : Fin 2).succAbove l) = minorCols008 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet040 (b c d e U : ℂ) :
    (cut040 (presentation b c d e U 0)).det = value (point b c d e U) D040 ∧
    HasDerivAt (fun T : ℂ => (cut040 (presentation b c d e U T)).det) (value (point b c d e U) J040) 0 := by
  have he (j : Fin 2) : cut040 (presentation b c d e U 0) 0 j = entriesA040 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 4 3
    · exact presentation_entry_zero b c d e U 4 5
  have he' (j : Fin 2) : HasDerivAt (fun T : ℂ => cut040 (presentation b c d e U T) 0 j)
      (entriesH040 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 4 3
    · exact presentation_entry_hasDerivAt b c d e U 4 5
  have hd (j : Fin 2) : ((cut040 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD040 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge040_0] using (detJet032 b c d e U).1
    · simpa only [cutEdge040_1] using (detJet008 b c d e U).1
  have hd' (j : Fin 2) : HasDerivAt (fun T : ℂ =>
      ((cut040 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ040 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge040_0] using (detJet032 b c d e U).2
    · simpa only [cutEdge040_1] using (detJet008 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut040 (presentation b c d e U T))
    (entriesA040 (point b c d e U)) (entriesH040 (point b c d e U)) (childD040 (point b c d e U)) (childJ040 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity040 (point b c d e U)).symm
  · rw [linear_identity040 (point b c d e U)]
    exact step.2
private theorem cutEdge048_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut048 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut032 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols048 ((0 : Fin 2).succAbove l) = minorCols032 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge048_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut048 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut016 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols048 ((1 : Fin 2).succAbove l) = minorCols016 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet048 (b c d e U : ℂ) :
    (cut048 (presentation b c d e U 0)).det = value (point b c d e U) D048 ∧
    HasDerivAt (fun T : ℂ => (cut048 (presentation b c d e U T)).det) (value (point b c d e U) J048) 0 := by
  have he (j : Fin 2) : cut048 (presentation b c d e U 0) 0 j = entriesA048 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 4 4
    · exact presentation_entry_zero b c d e U 4 5
  have he' (j : Fin 2) : HasDerivAt (fun T : ℂ => cut048 (presentation b c d e U T) 0 j)
      (entriesH048 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 4 4
    · exact presentation_entry_hasDerivAt b c d e U 4 5
  have hd (j : Fin 2) : ((cut048 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD048 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge048_0] using (detJet032 b c d e U).1
    · simpa only [cutEdge048_1] using (detJet016 b c d e U).1
  have hd' (j : Fin 2) : HasDerivAt (fun T : ℂ =>
      ((cut048 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ048 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge048_0] using (detJet032 b c d e U).2
    · simpa only [cutEdge048_1] using (detJet016 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut048 (presentation b c d e U T))
    (entriesA048 (point b c d e U)) (entriesH048 (point b c d e U)) (childD048 (point b c d e U)) (childJ048 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity048 (point b c d e U)).symm
  · rw [linear_identity048 (point b c d e U)]
    exact step.2
private theorem cutEdge007_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut007 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut006 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols007 ((0 : Fin 3).succAbove l) = minorCols006 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge007_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut007 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut005 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols007 ((1 : Fin 3).succAbove l) = minorCols005 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge007_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut007 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut003 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols007 ((2 : Fin 3).succAbove l) = minorCols003 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet007 (b c d e U : ℂ) :
    (cut007 (presentation b c d e U 0)).det = value (point b c d e U) D007 ∧
    HasDerivAt (fun T : ℂ => (cut007 (presentation b c d e U T)).det) (value (point b c d e U) J007) 0 := by
  have he (j : Fin 3) : cut007 (presentation b c d e U 0) 0 j = entriesA007 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 3 0
    · exact presentation_entry_zero b c d e U 3 1
    · exact presentation_entry_zero b c d e U 3 2
  have he' (j : Fin 3) : HasDerivAt (fun T : ℂ => cut007 (presentation b c d e U T) 0 j)
      (entriesH007 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 3 0
    · exact presentation_entry_hasDerivAt b c d e U 3 1
    · exact presentation_entry_hasDerivAt b c d e U 3 2
  have hd (j : Fin 3) : ((cut007 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD007 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge007_0] using (detJet006 b c d e U).1
    · simpa only [cutEdge007_1] using (detJet005 b c d e U).1
    · simpa only [cutEdge007_2] using (detJet003 b c d e U).1
  have hd' (j : Fin 3) : HasDerivAt (fun T : ℂ =>
      ((cut007 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ007 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge007_0] using (detJet006 b c d e U).2
    · simpa only [cutEdge007_1] using (detJet005 b c d e U).2
    · simpa only [cutEdge007_2] using (detJet003 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut007 (presentation b c d e U T))
    (entriesA007 (point b c d e U)) (entriesH007 (point b c d e U)) (childD007 (point b c d e U)) (childJ007 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity007 (point b c d e U)).symm
  · rw [linear_identity007 (point b c d e U)]
    exact step.2
private theorem cutEdge011_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut011 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut010 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols011 ((0 : Fin 3).succAbove l) = minorCols010 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge011_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut011 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut009 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols011 ((1 : Fin 3).succAbove l) = minorCols009 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge011_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut011 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut003 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols011 ((2 : Fin 3).succAbove l) = minorCols003 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet011 (b c d e U : ℂ) :
    (cut011 (presentation b c d e U 0)).det = value (point b c d e U) D011 ∧
    HasDerivAt (fun T : ℂ => (cut011 (presentation b c d e U T)).det) (value (point b c d e U) J011) 0 := by
  have he (j : Fin 3) : cut011 (presentation b c d e U 0) 0 j = entriesA011 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 3 0
    · exact presentation_entry_zero b c d e U 3 1
    · exact presentation_entry_zero b c d e U 3 3
  have he' (j : Fin 3) : HasDerivAt (fun T : ℂ => cut011 (presentation b c d e U T) 0 j)
      (entriesH011 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 3 0
    · exact presentation_entry_hasDerivAt b c d e U 3 1
    · exact presentation_entry_hasDerivAt b c d e U 3 3
  have hd (j : Fin 3) : ((cut011 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD011 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge011_0] using (detJet010 b c d e U).1
    · simpa only [cutEdge011_1] using (detJet009 b c d e U).1
    · simpa only [cutEdge011_2] using (detJet003 b c d e U).1
  have hd' (j : Fin 3) : HasDerivAt (fun T : ℂ =>
      ((cut011 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ011 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge011_0] using (detJet010 b c d e U).2
    · simpa only [cutEdge011_1] using (detJet009 b c d e U).2
    · simpa only [cutEdge011_2] using (detJet003 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut011 (presentation b c d e U T))
    (entriesA011 (point b c d e U)) (entriesH011 (point b c d e U)) (childD011 (point b c d e U)) (childJ011 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity011 (point b c d e U)).symm
  · rw [linear_identity011 (point b c d e U)]
    exact step.2
private theorem cutEdge013_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut013 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut012 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols013 ((0 : Fin 3).succAbove l) = minorCols012 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge013_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut013 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut009 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols013 ((1 : Fin 3).succAbove l) = minorCols009 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge013_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut013 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut005 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols013 ((2 : Fin 3).succAbove l) = minorCols005 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet013 (b c d e U : ℂ) :
    (cut013 (presentation b c d e U 0)).det = value (point b c d e U) D013 ∧
    HasDerivAt (fun T : ℂ => (cut013 (presentation b c d e U T)).det) (value (point b c d e U) J013) 0 := by
  have he (j : Fin 3) : cut013 (presentation b c d e U 0) 0 j = entriesA013 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 3 0
    · exact presentation_entry_zero b c d e U 3 2
    · exact presentation_entry_zero b c d e U 3 3
  have he' (j : Fin 3) : HasDerivAt (fun T : ℂ => cut013 (presentation b c d e U T) 0 j)
      (entriesH013 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 3 0
    · exact presentation_entry_hasDerivAt b c d e U 3 2
    · exact presentation_entry_hasDerivAt b c d e U 3 3
  have hd (j : Fin 3) : ((cut013 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD013 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge013_0] using (detJet012 b c d e U).1
    · simpa only [cutEdge013_1] using (detJet009 b c d e U).1
    · simpa only [cutEdge013_2] using (detJet005 b c d e U).1
  have hd' (j : Fin 3) : HasDerivAt (fun T : ℂ =>
      ((cut013 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ013 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge013_0] using (detJet012 b c d e U).2
    · simpa only [cutEdge013_1] using (detJet009 b c d e U).2
    · simpa only [cutEdge013_2] using (detJet005 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut013 (presentation b c d e U T))
    (entriesA013 (point b c d e U)) (entriesH013 (point b c d e U)) (childD013 (point b c d e U)) (childJ013 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity013 (point b c d e U)).symm
  · rw [linear_identity013 (point b c d e U)]
    exact step.2
end N6.ResultantMinors
