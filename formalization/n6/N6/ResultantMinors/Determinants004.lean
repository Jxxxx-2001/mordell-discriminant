import N6.ResultantMinors.Determinants003
import N6.ResultantMinors.Arithmetic004
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem cutEdge037_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut037 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut036 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols037 ((0 : Fin 3).succAbove l) = minorCols036 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge037_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut037 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut033 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols037 ((1 : Fin 3).succAbove l) = minorCols033 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge037_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut037 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut005 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols037 ((2 : Fin 3).succAbove l) = minorCols005 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet037 (b c d e U : ℂ) :
    (cut037 (presentation b c d e U 0)).det = value (point b c d e U) D037 ∧
    HasDerivAt (fun T : ℂ => (cut037 (presentation b c d e U T)).det) (value (point b c d e U) J037) 0 := by
  have he (j : Fin 3) : cut037 (presentation b c d e U 0) 0 j = entriesA037 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 3 0
    · exact presentation_entry_zero b c d e U 3 2
    · exact presentation_entry_zero b c d e U 3 5
  have he' (j : Fin 3) : HasDerivAt (fun T : ℂ => cut037 (presentation b c d e U T) 0 j)
      (entriesH037 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 3 0
    · exact presentation_entry_hasDerivAt b c d e U 3 2
    · exact presentation_entry_hasDerivAt b c d e U 3 5
  have hd (j : Fin 3) : ((cut037 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD037 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge037_0] using (detJet036 b c d e U).1
    · simpa only [cutEdge037_1] using (detJet033 b c d e U).1
    · simpa only [cutEdge037_2] using (detJet005 b c d e U).1
  have hd' (j : Fin 3) : HasDerivAt (fun T : ℂ =>
      ((cut037 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ037 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge037_0] using (detJet036 b c d e U).2
    · simpa only [cutEdge037_1] using (detJet033 b c d e U).2
    · simpa only [cutEdge037_2] using (detJet005 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut037 (presentation b c d e U T))
    (entriesA037 (point b c d e U)) (entriesH037 (point b c d e U)) (childD037 (point b c d e U)) (childJ037 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity037 (point b c d e U)).symm
  · rw [linear_identity037 (point b c d e U)]
    exact step.2
private theorem cutEdge038_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut038 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut036 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols038 ((0 : Fin 3).succAbove l) = minorCols036 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge038_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut038 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut034 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols038 ((1 : Fin 3).succAbove l) = minorCols034 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge038_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut038 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut006 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols038 ((2 : Fin 3).succAbove l) = minorCols006 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet038 (b c d e U : ℂ) :
    (cut038 (presentation b c d e U 0)).det = value (point b c d e U) D038 ∧
    HasDerivAt (fun T : ℂ => (cut038 (presentation b c d e U T)).det) (value (point b c d e U) J038) 0 := by
  have he (j : Fin 3) : cut038 (presentation b c d e U 0) 0 j = entriesA038 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 3 1
    · exact presentation_entry_zero b c d e U 3 2
    · exact presentation_entry_zero b c d e U 3 5
  have he' (j : Fin 3) : HasDerivAt (fun T : ℂ => cut038 (presentation b c d e U T) 0 j)
      (entriesH038 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 3 1
    · exact presentation_entry_hasDerivAt b c d e U 3 2
    · exact presentation_entry_hasDerivAt b c d e U 3 5
  have hd (j : Fin 3) : ((cut038 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD038 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge038_0] using (detJet036 b c d e U).1
    · simpa only [cutEdge038_1] using (detJet034 b c d e U).1
    · simpa only [cutEdge038_2] using (detJet006 b c d e U).1
  have hd' (j : Fin 3) : HasDerivAt (fun T : ℂ =>
      ((cut038 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ038 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge038_0] using (detJet036 b c d e U).2
    · simpa only [cutEdge038_1] using (detJet034 b c d e U).2
    · simpa only [cutEdge038_2] using (detJet006 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut038 (presentation b c d e U T))
    (entriesA038 (point b c d e U)) (entriesH038 (point b c d e U)) (childD038 (point b c d e U)) (childJ038 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity038 (point b c d e U)).symm
  · rw [linear_identity038 (point b c d e U)]
    exact step.2
private theorem cutEdge041_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut041 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut040 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols041 ((0 : Fin 3).succAbove l) = minorCols040 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge041_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut041 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut033 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols041 ((1 : Fin 3).succAbove l) = minorCols033 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge041_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut041 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut009 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols041 ((2 : Fin 3).succAbove l) = minorCols009 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet041 (b c d e U : ℂ) :
    (cut041 (presentation b c d e U 0)).det = value (point b c d e U) D041 ∧
    HasDerivAt (fun T : ℂ => (cut041 (presentation b c d e U T)).det) (value (point b c d e U) J041) 0 := by
  have he (j : Fin 3) : cut041 (presentation b c d e U 0) 0 j = entriesA041 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 3 0
    · exact presentation_entry_zero b c d e U 3 3
    · exact presentation_entry_zero b c d e U 3 5
  have he' (j : Fin 3) : HasDerivAt (fun T : ℂ => cut041 (presentation b c d e U T) 0 j)
      (entriesH041 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 3 0
    · exact presentation_entry_hasDerivAt b c d e U 3 3
    · exact presentation_entry_hasDerivAt b c d e U 3 5
  have hd (j : Fin 3) : ((cut041 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD041 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge041_0] using (detJet040 b c d e U).1
    · simpa only [cutEdge041_1] using (detJet033 b c d e U).1
    · simpa only [cutEdge041_2] using (detJet009 b c d e U).1
  have hd' (j : Fin 3) : HasDerivAt (fun T : ℂ =>
      ((cut041 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ041 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge041_0] using (detJet040 b c d e U).2
    · simpa only [cutEdge041_1] using (detJet033 b c d e U).2
    · simpa only [cutEdge041_2] using (detJet009 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut041 (presentation b c d e U T))
    (entriesA041 (point b c d e U)) (entriesH041 (point b c d e U)) (childD041 (point b c d e U)) (childJ041 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity041 (point b c d e U)).symm
  · rw [linear_identity041 (point b c d e U)]
    exact step.2
private theorem cutEdge042_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut042 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut040 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols042 ((0 : Fin 3).succAbove l) = minorCols040 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge042_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut042 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut034 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols042 ((1 : Fin 3).succAbove l) = minorCols034 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge042_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut042 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut010 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols042 ((2 : Fin 3).succAbove l) = minorCols010 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet042 (b c d e U : ℂ) :
    (cut042 (presentation b c d e U 0)).det = value (point b c d e U) D042 ∧
    HasDerivAt (fun T : ℂ => (cut042 (presentation b c d e U T)).det) (value (point b c d e U) J042) 0 := by
  have he (j : Fin 3) : cut042 (presentation b c d e U 0) 0 j = entriesA042 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 3 1
    · exact presentation_entry_zero b c d e U 3 3
    · exact presentation_entry_zero b c d e U 3 5
  have he' (j : Fin 3) : HasDerivAt (fun T : ℂ => cut042 (presentation b c d e U T) 0 j)
      (entriesH042 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 3 1
    · exact presentation_entry_hasDerivAt b c d e U 3 3
    · exact presentation_entry_hasDerivAt b c d e U 3 5
  have hd (j : Fin 3) : ((cut042 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD042 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge042_0] using (detJet040 b c d e U).1
    · simpa only [cutEdge042_1] using (detJet034 b c d e U).1
    · simpa only [cutEdge042_2] using (detJet010 b c d e U).1
  have hd' (j : Fin 3) : HasDerivAt (fun T : ℂ =>
      ((cut042 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ042 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge042_0] using (detJet040 b c d e U).2
    · simpa only [cutEdge042_1] using (detJet034 b c d e U).2
    · simpa only [cutEdge042_2] using (detJet010 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut042 (presentation b c d e U T))
    (entriesA042 (point b c d e U)) (entriesH042 (point b c d e U)) (childD042 (point b c d e U)) (childJ042 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity042 (point b c d e U)).symm
  · rw [linear_identity042 (point b c d e U)]
    exact step.2
private theorem cutEdge044_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut044 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut040 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols044 ((0 : Fin 3).succAbove l) = minorCols040 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge044_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut044 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut036 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols044 ((1 : Fin 3).succAbove l) = minorCols036 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge044_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut044 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut012 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols044 ((2 : Fin 3).succAbove l) = minorCols012 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet044 (b c d e U : ℂ) :
    (cut044 (presentation b c d e U 0)).det = value (point b c d e U) D044 ∧
    HasDerivAt (fun T : ℂ => (cut044 (presentation b c d e U T)).det) (value (point b c d e U) J044) 0 := by
  have he (j : Fin 3) : cut044 (presentation b c d e U 0) 0 j = entriesA044 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 3 2
    · exact presentation_entry_zero b c d e U 3 3
    · exact presentation_entry_zero b c d e U 3 5
  have he' (j : Fin 3) : HasDerivAt (fun T : ℂ => cut044 (presentation b c d e U T) 0 j)
      (entriesH044 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 3 2
    · exact presentation_entry_hasDerivAt b c d e U 3 3
    · exact presentation_entry_hasDerivAt b c d e U 3 5
  have hd (j : Fin 3) : ((cut044 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD044 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge044_0] using (detJet040 b c d e U).1
    · simpa only [cutEdge044_1] using (detJet036 b c d e U).1
    · simpa only [cutEdge044_2] using (detJet012 b c d e U).1
  have hd' (j : Fin 3) : HasDerivAt (fun T : ℂ =>
      ((cut044 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ044 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge044_0] using (detJet040 b c d e U).2
    · simpa only [cutEdge044_1] using (detJet036 b c d e U).2
    · simpa only [cutEdge044_2] using (detJet012 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut044 (presentation b c d e U T))
    (entriesA044 (point b c d e U)) (entriesH044 (point b c d e U)) (childD044 (point b c d e U)) (childJ044 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity044 (point b c d e U)).symm
  · rw [linear_identity044 (point b c d e U)]
    exact step.2
private theorem cutEdge049_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut049 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut048 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols049 ((0 : Fin 3).succAbove l) = minorCols048 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge049_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut049 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut033 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols049 ((1 : Fin 3).succAbove l) = minorCols033 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge049_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut049 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut017 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols049 ((2 : Fin 3).succAbove l) = minorCols017 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet049 (b c d e U : ℂ) :
    (cut049 (presentation b c d e U 0)).det = value (point b c d e U) D049 ∧
    HasDerivAt (fun T : ℂ => (cut049 (presentation b c d e U T)).det) (value (point b c d e U) J049) 0 := by
  have he (j : Fin 3) : cut049 (presentation b c d e U 0) 0 j = entriesA049 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 3 0
    · exact presentation_entry_zero b c d e U 3 4
    · exact presentation_entry_zero b c d e U 3 5
  have he' (j : Fin 3) : HasDerivAt (fun T : ℂ => cut049 (presentation b c d e U T) 0 j)
      (entriesH049 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 3 0
    · exact presentation_entry_hasDerivAt b c d e U 3 4
    · exact presentation_entry_hasDerivAt b c d e U 3 5
  have hd (j : Fin 3) : ((cut049 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD049 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge049_0] using (detJet048 b c d e U).1
    · simpa only [cutEdge049_1] using (detJet033 b c d e U).1
    · simpa only [cutEdge049_2] using (detJet017 b c d e U).1
  have hd' (j : Fin 3) : HasDerivAt (fun T : ℂ =>
      ((cut049 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ049 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge049_0] using (detJet048 b c d e U).2
    · simpa only [cutEdge049_1] using (detJet033 b c d e U).2
    · simpa only [cutEdge049_2] using (detJet017 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut049 (presentation b c d e U T))
    (entriesA049 (point b c d e U)) (entriesH049 (point b c d e U)) (childD049 (point b c d e U)) (childJ049 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity049 (point b c d e U)).symm
  · rw [linear_identity049 (point b c d e U)]
    exact step.2
private theorem cutEdge050_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut050 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut048 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols050 ((0 : Fin 3).succAbove l) = minorCols048 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge050_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut050 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut034 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols050 ((1 : Fin 3).succAbove l) = minorCols034 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge050_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut050 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut018 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols050 ((2 : Fin 3).succAbove l) = minorCols018 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet050 (b c d e U : ℂ) :
    (cut050 (presentation b c d e U 0)).det = value (point b c d e U) D050 ∧
    HasDerivAt (fun T : ℂ => (cut050 (presentation b c d e U T)).det) (value (point b c d e U) J050) 0 := by
  have he (j : Fin 3) : cut050 (presentation b c d e U 0) 0 j = entriesA050 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 3 1
    · exact presentation_entry_zero b c d e U 3 4
    · exact presentation_entry_zero b c d e U 3 5
  have he' (j : Fin 3) : HasDerivAt (fun T : ℂ => cut050 (presentation b c d e U T) 0 j)
      (entriesH050 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 3 1
    · exact presentation_entry_hasDerivAt b c d e U 3 4
    · exact presentation_entry_hasDerivAt b c d e U 3 5
  have hd (j : Fin 3) : ((cut050 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD050 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge050_0] using (detJet048 b c d e U).1
    · simpa only [cutEdge050_1] using (detJet034 b c d e U).1
    · simpa only [cutEdge050_2] using (detJet018 b c d e U).1
  have hd' (j : Fin 3) : HasDerivAt (fun T : ℂ =>
      ((cut050 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ050 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge050_0] using (detJet048 b c d e U).2
    · simpa only [cutEdge050_1] using (detJet034 b c d e U).2
    · simpa only [cutEdge050_2] using (detJet018 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut050 (presentation b c d e U T))
    (entriesA050 (point b c d e U)) (entriesH050 (point b c d e U)) (childD050 (point b c d e U)) (childJ050 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity050 (point b c d e U)).symm
  · rw [linear_identity050 (point b c d e U)]
    exact step.2
private theorem cutEdge052_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut052 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut048 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols052 ((0 : Fin 3).succAbove l) = minorCols048 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge052_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut052 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut036 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols052 ((1 : Fin 3).succAbove l) = minorCols036 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge052_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut052 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut020 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows3 i.succ = suffixRows2 i := by fin_cases i <;> rfl
  have hc : minorCols052 ((2 : Fin 3).succAbove l) = minorCols020 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet052 (b c d e U : ℂ) :
    (cut052 (presentation b c d e U 0)).det = value (point b c d e U) D052 ∧
    HasDerivAt (fun T : ℂ => (cut052 (presentation b c d e U T)).det) (value (point b c d e U) J052) 0 := by
  have he (j : Fin 3) : cut052 (presentation b c d e U 0) 0 j = entriesA052 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 3 2
    · exact presentation_entry_zero b c d e U 3 4
    · exact presentation_entry_zero b c d e U 3 5
  have he' (j : Fin 3) : HasDerivAt (fun T : ℂ => cut052 (presentation b c d e U T) 0 j)
      (entriesH052 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 3 2
    · exact presentation_entry_hasDerivAt b c d e U 3 4
    · exact presentation_entry_hasDerivAt b c d e U 3 5
  have hd (j : Fin 3) : ((cut052 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD052 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge052_0] using (detJet048 b c d e U).1
    · simpa only [cutEdge052_1] using (detJet036 b c d e U).1
    · simpa only [cutEdge052_2] using (detJet020 b c d e U).1
  have hd' (j : Fin 3) : HasDerivAt (fun T : ℂ =>
      ((cut052 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ052 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge052_0] using (detJet048 b c d e U).2
    · simpa only [cutEdge052_1] using (detJet036 b c d e U).2
    · simpa only [cutEdge052_2] using (detJet020 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut052 (presentation b c d e U T))
    (entriesA052 (point b c d e U)) (entriesH052 (point b c d e U)) (childD052 (point b c d e U)) (childJ052 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity052 (point b c d e U)).symm
  · rw [linear_identity052 (point b c d e U)]
    exact step.2
end N6.ResultantMinors
