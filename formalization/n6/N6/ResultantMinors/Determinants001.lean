import N6.ResultantMinors.Determinants000
import N6.ResultantMinors.Arithmetic001
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem cutEdge006_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut006 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut004 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols006 ((0 : Fin 2).succAbove l) = minorCols004 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge006_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut006 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut002 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols006 ((1 : Fin 2).succAbove l) = minorCols002 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet006 (b c d e U : ℂ) :
    (cut006 (presentation b c d e U 0)).det = value (point b c d e U) D006 ∧
    HasDerivAt (fun T : ℂ => (cut006 (presentation b c d e U T)).det) (value (point b c d e U) J006) 0 := by
  have he (j : Fin 2) : cut006 (presentation b c d e U 0) 0 j = entriesA006 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 4 1
    · exact presentation_entry_zero b c d e U 4 2
  have he' (j : Fin 2) : HasDerivAt (fun T : ℂ => cut006 (presentation b c d e U T) 0 j)
      (entriesH006 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 4 1
    · exact presentation_entry_hasDerivAt b c d e U 4 2
  have hd (j : Fin 2) : ((cut006 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD006 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge006_0] using (detJet004 b c d e U).1
    · simpa only [cutEdge006_1] using (detJet002 b c d e U).1
  have hd' (j : Fin 2) : HasDerivAt (fun T : ℂ =>
      ((cut006 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ006 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge006_0] using (detJet004 b c d e U).2
    · simpa only [cutEdge006_1] using (detJet002 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut006 (presentation b c d e U T))
    (entriesA006 (point b c d e U)) (entriesH006 (point b c d e U)) (childD006 (point b c d e U)) (childJ006 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity006 (point b c d e U)).symm
  · rw [linear_identity006 (point b c d e U)]
    exact step.2
private theorem cutEdge009_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut009 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut008 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols009 ((0 : Fin 2).succAbove l) = minorCols008 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge009_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut009 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut001 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols009 ((1 : Fin 2).succAbove l) = minorCols001 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet009 (b c d e U : ℂ) :
    (cut009 (presentation b c d e U 0)).det = value (point b c d e U) D009 ∧
    HasDerivAt (fun T : ℂ => (cut009 (presentation b c d e U T)).det) (value (point b c d e U) J009) 0 := by
  have he (j : Fin 2) : cut009 (presentation b c d e U 0) 0 j = entriesA009 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 4 0
    · exact presentation_entry_zero b c d e U 4 3
  have he' (j : Fin 2) : HasDerivAt (fun T : ℂ => cut009 (presentation b c d e U T) 0 j)
      (entriesH009 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 4 0
    · exact presentation_entry_hasDerivAt b c d e U 4 3
  have hd (j : Fin 2) : ((cut009 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD009 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge009_0] using (detJet008 b c d e U).1
    · simpa only [cutEdge009_1] using (detJet001 b c d e U).1
  have hd' (j : Fin 2) : HasDerivAt (fun T : ℂ =>
      ((cut009 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ009 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge009_0] using (detJet008 b c d e U).2
    · simpa only [cutEdge009_1] using (detJet001 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut009 (presentation b c d e U T))
    (entriesA009 (point b c d e U)) (entriesH009 (point b c d e U)) (childD009 (point b c d e U)) (childJ009 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity009 (point b c d e U)).symm
  · rw [linear_identity009 (point b c d e U)]
    exact step.2
private theorem cutEdge010_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut010 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut008 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols010 ((0 : Fin 2).succAbove l) = minorCols008 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge010_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut010 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut002 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols010 ((1 : Fin 2).succAbove l) = minorCols002 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet010 (b c d e U : ℂ) :
    (cut010 (presentation b c d e U 0)).det = value (point b c d e U) D010 ∧
    HasDerivAt (fun T : ℂ => (cut010 (presentation b c d e U T)).det) (value (point b c d e U) J010) 0 := by
  have he (j : Fin 2) : cut010 (presentation b c d e U 0) 0 j = entriesA010 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 4 1
    · exact presentation_entry_zero b c d e U 4 3
  have he' (j : Fin 2) : HasDerivAt (fun T : ℂ => cut010 (presentation b c d e U T) 0 j)
      (entriesH010 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 4 1
    · exact presentation_entry_hasDerivAt b c d e U 4 3
  have hd (j : Fin 2) : ((cut010 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD010 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge010_0] using (detJet008 b c d e U).1
    · simpa only [cutEdge010_1] using (detJet002 b c d e U).1
  have hd' (j : Fin 2) : HasDerivAt (fun T : ℂ =>
      ((cut010 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ010 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge010_0] using (detJet008 b c d e U).2
    · simpa only [cutEdge010_1] using (detJet002 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut010 (presentation b c d e U T))
    (entriesA010 (point b c d e U)) (entriesH010 (point b c d e U)) (childD010 (point b c d e U)) (childJ010 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity010 (point b c d e U)).symm
  · rw [linear_identity010 (point b c d e U)]
    exact step.2
private theorem cutEdge012_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut012 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut008 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols012 ((0 : Fin 2).succAbove l) = minorCols008 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge012_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut012 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut004 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols012 ((1 : Fin 2).succAbove l) = minorCols004 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet012 (b c d e U : ℂ) :
    (cut012 (presentation b c d e U 0)).det = value (point b c d e U) D012 ∧
    HasDerivAt (fun T : ℂ => (cut012 (presentation b c d e U T)).det) (value (point b c d e U) J012) 0 := by
  have he (j : Fin 2) : cut012 (presentation b c d e U 0) 0 j = entriesA012 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 4 2
    · exact presentation_entry_zero b c d e U 4 3
  have he' (j : Fin 2) : HasDerivAt (fun T : ℂ => cut012 (presentation b c d e U T) 0 j)
      (entriesH012 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 4 2
    · exact presentation_entry_hasDerivAt b c d e U 4 3
  have hd (j : Fin 2) : ((cut012 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD012 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge012_0] using (detJet008 b c d e U).1
    · simpa only [cutEdge012_1] using (detJet004 b c d e U).1
  have hd' (j : Fin 2) : HasDerivAt (fun T : ℂ =>
      ((cut012 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ012 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge012_0] using (detJet008 b c d e U).2
    · simpa only [cutEdge012_1] using (detJet004 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut012 (presentation b c d e U T))
    (entriesA012 (point b c d e U)) (entriesH012 (point b c d e U)) (childD012 (point b c d e U)) (childJ012 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity012 (point b c d e U)).symm
  · rw [linear_identity012 (point b c d e U)]
    exact step.2
private theorem cutEdge017_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut017 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut016 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols017 ((0 : Fin 2).succAbove l) = minorCols016 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge017_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut017 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut001 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols017 ((1 : Fin 2).succAbove l) = minorCols001 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet017 (b c d e U : ℂ) :
    (cut017 (presentation b c d e U 0)).det = value (point b c d e U) D017 ∧
    HasDerivAt (fun T : ℂ => (cut017 (presentation b c d e U T)).det) (value (point b c d e U) J017) 0 := by
  have he (j : Fin 2) : cut017 (presentation b c d e U 0) 0 j = entriesA017 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 4 0
    · exact presentation_entry_zero b c d e U 4 4
  have he' (j : Fin 2) : HasDerivAt (fun T : ℂ => cut017 (presentation b c d e U T) 0 j)
      (entriesH017 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 4 0
    · exact presentation_entry_hasDerivAt b c d e U 4 4
  have hd (j : Fin 2) : ((cut017 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD017 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge017_0] using (detJet016 b c d e U).1
    · simpa only [cutEdge017_1] using (detJet001 b c d e U).1
  have hd' (j : Fin 2) : HasDerivAt (fun T : ℂ =>
      ((cut017 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ017 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge017_0] using (detJet016 b c d e U).2
    · simpa only [cutEdge017_1] using (detJet001 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut017 (presentation b c d e U T))
    (entriesA017 (point b c d e U)) (entriesH017 (point b c d e U)) (childD017 (point b c d e U)) (childJ017 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity017 (point b c d e U)).symm
  · rw [linear_identity017 (point b c d e U)]
    exact step.2
private theorem cutEdge018_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut018 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut016 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols018 ((0 : Fin 2).succAbove l) = minorCols016 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge018_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut018 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut002 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols018 ((1 : Fin 2).succAbove l) = minorCols002 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet018 (b c d e U : ℂ) :
    (cut018 (presentation b c d e U 0)).det = value (point b c d e U) D018 ∧
    HasDerivAt (fun T : ℂ => (cut018 (presentation b c d e U T)).det) (value (point b c d e U) J018) 0 := by
  have he (j : Fin 2) : cut018 (presentation b c d e U 0) 0 j = entriesA018 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 4 1
    · exact presentation_entry_zero b c d e U 4 4
  have he' (j : Fin 2) : HasDerivAt (fun T : ℂ => cut018 (presentation b c d e U T) 0 j)
      (entriesH018 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 4 1
    · exact presentation_entry_hasDerivAt b c d e U 4 4
  have hd (j : Fin 2) : ((cut018 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD018 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge018_0] using (detJet016 b c d e U).1
    · simpa only [cutEdge018_1] using (detJet002 b c d e U).1
  have hd' (j : Fin 2) : HasDerivAt (fun T : ℂ =>
      ((cut018 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ018 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge018_0] using (detJet016 b c d e U).2
    · simpa only [cutEdge018_1] using (detJet002 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut018 (presentation b c d e U T))
    (entriesA018 (point b c d e U)) (entriesH018 (point b c d e U)) (childD018 (point b c d e U)) (childJ018 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity018 (point b c d e U)).symm
  · rw [linear_identity018 (point b c d e U)]
    exact step.2
private theorem cutEdge020_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut020 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut016 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols020 ((0 : Fin 2).succAbove l) = minorCols016 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge020_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut020 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut004 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols020 ((1 : Fin 2).succAbove l) = minorCols004 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet020 (b c d e U : ℂ) :
    (cut020 (presentation b c d e U 0)).det = value (point b c d e U) D020 ∧
    HasDerivAt (fun T : ℂ => (cut020 (presentation b c d e U T)).det) (value (point b c d e U) J020) 0 := by
  have he (j : Fin 2) : cut020 (presentation b c d e U 0) 0 j = entriesA020 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 4 2
    · exact presentation_entry_zero b c d e U 4 4
  have he' (j : Fin 2) : HasDerivAt (fun T : ℂ => cut020 (presentation b c d e U T) 0 j)
      (entriesH020 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 4 2
    · exact presentation_entry_hasDerivAt b c d e U 4 4
  have hd (j : Fin 2) : ((cut020 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD020 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge020_0] using (detJet016 b c d e U).1
    · simpa only [cutEdge020_1] using (detJet004 b c d e U).1
  have hd' (j : Fin 2) : HasDerivAt (fun T : ℂ =>
      ((cut020 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ020 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge020_0] using (detJet016 b c d e U).2
    · simpa only [cutEdge020_1] using (detJet004 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut020 (presentation b c d e U T))
    (entriesA020 (point b c d e U)) (entriesH020 (point b c d e U)) (childD020 (point b c d e U)) (childJ020 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity020 (point b c d e U)).symm
  · rw [linear_identity020 (point b c d e U)]
    exact step.2
private theorem cutEdge024_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut024 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut016 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols024 ((0 : Fin 2).succAbove l) = minorCols016 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
private theorem cutEdge024_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut024 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut008 A := by
  apply Matrix.ext
  intro i l
  have hr : suffixRows2 i.succ = suffixRows1 i := by fin_cases i <;> rfl
  have hc : minorCols024 ((1 : Fin 2).succAbove l) = minorCols008 l := by fin_cases l <;> rfl
  exact congrArg₂ A hr hc
theorem detJet024 (b c d e U : ℂ) :
    (cut024 (presentation b c d e U 0)).det = value (point b c d e U) D024 ∧
    HasDerivAt (fun T : ℂ => (cut024 (presentation b c d e U T)).det) (value (point b c d e U) J024) 0 := by
  have he (j : Fin 2) : cut024 (presentation b c d e U 0) 0 j = entriesA024 (point b c d e U) j := by
    fin_cases j
    · exact presentation_entry_zero b c d e U 4 3
    · exact presentation_entry_zero b c d e U 4 4
  have he' (j : Fin 2) : HasDerivAt (fun T : ℂ => cut024 (presentation b c d e U T) 0 j)
      (entriesH024 (point b c d e U) j) 0 := by
    fin_cases j
    · exact presentation_entry_hasDerivAt b c d e U 4 3
    · exact presentation_entry_hasDerivAt b c d e U 4 4
  have hd (j : Fin 2) : ((cut024 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD024 (point b c d e U) j := by
    fin_cases j
    · simpa only [cutEdge024_0] using (detJet016 b c d e U).1
    · simpa only [cutEdge024_1] using (detJet008 b c d e U).1
  have hd' (j : Fin 2) : HasDerivAt (fun T : ℂ =>
      ((cut024 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ024 (point b c d e U) j) 0 := by
    fin_cases j
    · simpa only [cutEdge024_0] using (detJet016 b c d e U).2
    · simpa only [cutEdge024_1] using (detJet008 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut024 (presentation b c d e U T))
    (entriesA024 (point b c d e U)) (entriesH024 (point b c d e U)) (childD024 (point b c d e U)) (childJ024 (point b c d e U)) he he' hd hd'
  constructor
  · exact step.1.trans (const_identity024 (point b c d e U)).symm
  · rw [linear_identity024 (point b c d e U)]
    exact step.2
end N6.ResultantMinors
