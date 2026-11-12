import N6.Exceptional.Determinants005_00
import N6.Exceptional.Arithmetic005
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.Resultant6
private theorem rows015 : ∀ i : Fin 3, suffixRows4 i.succ = suffixRows3 i := by decide +kernel
private theorem cols015_0 : ∀ l : Fin 3, minorCols015 ((0 : Fin 4).succAbove l) = minorCols014 l := by
  decide +kernel
private theorem cutEdge015_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut015 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut014 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows015 i) (cols015_0 l)
private theorem cols015_1 : ∀ l : Fin 3, minorCols015 ((1 : Fin 4).succAbove l) = minorCols013 l := by
  decide +kernel
private theorem cutEdge015_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut015 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut013 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows015 i) (cols015_1 l)
private theorem cols015_2 : ∀ l : Fin 3, minorCols015 ((2 : Fin 4).succAbove l) = minorCols011 l := by
  decide +kernel
private theorem cutEdge015_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut015 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut011 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows015 i) (cols015_2 l)
private theorem cols015_3 : ∀ l : Fin 3, minorCols015 ((3 : Fin 4).succAbove l) = minorCols007 l := by
  decide +kernel
private theorem cutEdge015_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut015 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut007 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows015 i) (cols015_3 l)
theorem detJet015 (b c d e U : ℂ) :
    (cut015 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D015 ∧
    HasDerivAt (fun T : ℂ => (cut015 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J015) 0 := by
  have he : ∀ j : Fin 4, cut015 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA015 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut015 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA015 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 3
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut015 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH015 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut015 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH015 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 3
  have hd : ∀ j : Fin 4, ((cut015 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD015 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut015 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD015 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge015_0] using (detJet014 b c d e U).1
    · simpa only [cutEdge015_1] using (detJet013 b c d e U).1
    · simpa only [cutEdge015_2] using (detJet011 b c d e U).1
    · simpa only [cutEdge015_3] using (detJet007 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut015 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ015 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut015 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ015 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge015_0] using (detJet014 b c d e U).2
    · simpa only [cutEdge015_1] using (detJet013 b c d e U).2
    · simpa only [cutEdge015_2] using (detJet011 b c d e U).2
    · simpa only [cutEdge015_3] using (detJet007 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut015 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA015 (point b c d e U)) (entriesH015 (point b c d e U)) (childD015 (point b c d e U)) (childJ015 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity015 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity015 (point b c d e U)).symm⟩
private theorem rows023 : ∀ i : Fin 3, suffixRows4 i.succ = suffixRows3 i := by decide +kernel
private theorem cols023_0 : ∀ l : Fin 3, minorCols023 ((0 : Fin 4).succAbove l) = minorCols022 l := by
  decide +kernel
private theorem cutEdge023_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut023 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut022 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows023 i) (cols023_0 l)
private theorem cols023_1 : ∀ l : Fin 3, minorCols023 ((1 : Fin 4).succAbove l) = minorCols021 l := by
  decide +kernel
private theorem cutEdge023_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut023 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut021 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows023 i) (cols023_1 l)
private theorem cols023_2 : ∀ l : Fin 3, minorCols023 ((2 : Fin 4).succAbove l) = minorCols019 l := by
  decide +kernel
private theorem cutEdge023_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut023 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut019 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows023 i) (cols023_2 l)
private theorem cols023_3 : ∀ l : Fin 3, minorCols023 ((3 : Fin 4).succAbove l) = minorCols007 l := by
  decide +kernel
private theorem cutEdge023_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut023 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut007 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows023 i) (cols023_3 l)
theorem detJet023 (b c d e U : ℂ) :
    (cut023 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D023 ∧
    HasDerivAt (fun T : ℂ => (cut023 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J023) 0 := by
  have he : ∀ j : Fin 4, cut023 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA023 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut023 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA023 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 4
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut023 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH023 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut023 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH023 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 4
  have hd : ∀ j : Fin 4, ((cut023 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD023 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut023 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD023 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge023_0] using (detJet022 b c d e U).1
    · simpa only [cutEdge023_1] using (detJet021 b c d e U).1
    · simpa only [cutEdge023_2] using (detJet019 b c d e U).1
    · simpa only [cutEdge023_3] using (detJet007 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut023 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ023 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut023 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ023 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge023_0] using (detJet022 b c d e U).2
    · simpa only [cutEdge023_1] using (detJet021 b c d e U).2
    · simpa only [cutEdge023_2] using (detJet019 b c d e U).2
    · simpa only [cutEdge023_3] using (detJet007 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut023 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA023 (point b c d e U)) (entriesH023 (point b c d e U)) (childD023 (point b c d e U)) (childJ023 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity023 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity023 (point b c d e U)).symm⟩
private theorem rows027 : ∀ i : Fin 3, suffixRows4 i.succ = suffixRows3 i := by decide +kernel
private theorem cols027_0 : ∀ l : Fin 3, minorCols027 ((0 : Fin 4).succAbove l) = minorCols026 l := by
  decide +kernel
private theorem cutEdge027_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut027 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut026 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows027 i) (cols027_0 l)
private theorem cols027_1 : ∀ l : Fin 3, minorCols027 ((1 : Fin 4).succAbove l) = minorCols025 l := by
  decide +kernel
private theorem cutEdge027_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut027 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut025 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows027 i) (cols027_1 l)
private theorem cols027_2 : ∀ l : Fin 3, minorCols027 ((2 : Fin 4).succAbove l) = minorCols019 l := by
  decide +kernel
private theorem cutEdge027_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut027 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut019 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows027 i) (cols027_2 l)
private theorem cols027_3 : ∀ l : Fin 3, minorCols027 ((3 : Fin 4).succAbove l) = minorCols011 l := by
  decide +kernel
private theorem cutEdge027_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut027 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut011 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows027 i) (cols027_3 l)
theorem detJet027 (b c d e U : ℂ) :
    (cut027 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D027 ∧
    HasDerivAt (fun T : ℂ => (cut027 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J027) 0 := by
  have he : ∀ j : Fin 4, cut027 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA027 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut027 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA027 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 4
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut027 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH027 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut027 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH027 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 4
  have hd : ∀ j : Fin 4, ((cut027 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD027 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut027 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD027 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge027_0] using (detJet026 b c d e U).1
    · simpa only [cutEdge027_1] using (detJet025 b c d e U).1
    · simpa only [cutEdge027_2] using (detJet019 b c d e U).1
    · simpa only [cutEdge027_3] using (detJet011 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut027 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ027 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut027 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ027 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge027_0] using (detJet026 b c d e U).2
    · simpa only [cutEdge027_1] using (detJet025 b c d e U).2
    · simpa only [cutEdge027_2] using (detJet019 b c d e U).2
    · simpa only [cutEdge027_3] using (detJet011 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut027 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA027 (point b c d e U)) (entriesH027 (point b c d e U)) (childD027 (point b c d e U)) (childJ027 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity027 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity027 (point b c d e U)).symm⟩
private theorem rows029 : ∀ i : Fin 3, suffixRows4 i.succ = suffixRows3 i := by decide +kernel
private theorem cols029_0 : ∀ l : Fin 3, minorCols029 ((0 : Fin 4).succAbove l) = minorCols028 l := by
  decide +kernel
private theorem cutEdge029_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut029 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut028 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows029 i) (cols029_0 l)
private theorem cols029_1 : ∀ l : Fin 3, minorCols029 ((1 : Fin 4).succAbove l) = minorCols025 l := by
  decide +kernel
private theorem cutEdge029_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut029 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut025 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows029 i) (cols029_1 l)
private theorem cols029_2 : ∀ l : Fin 3, minorCols029 ((2 : Fin 4).succAbove l) = minorCols021 l := by
  decide +kernel
private theorem cutEdge029_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut029 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut021 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows029 i) (cols029_2 l)
private theorem cols029_3 : ∀ l : Fin 3, minorCols029 ((3 : Fin 4).succAbove l) = minorCols013 l := by
  decide +kernel
private theorem cutEdge029_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut029 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut013 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows029 i) (cols029_3 l)
theorem detJet029 (b c d e U : ℂ) :
    (cut029 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D029 ∧
    HasDerivAt (fun T : ℂ => (cut029 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J029) 0 := by
  have he : ∀ j : Fin 4, cut029 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA029 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut029 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA029 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 4
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut029 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH029 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut029 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH029 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 4
  have hd : ∀ j : Fin 4, ((cut029 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD029 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut029 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD029 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge029_0] using (detJet028 b c d e U).1
    · simpa only [cutEdge029_1] using (detJet025 b c d e U).1
    · simpa only [cutEdge029_2] using (detJet021 b c d e U).1
    · simpa only [cutEdge029_3] using (detJet013 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut029 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ029 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut029 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ029 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge029_0] using (detJet028 b c d e U).2
    · simpa only [cutEdge029_1] using (detJet025 b c d e U).2
    · simpa only [cutEdge029_2] using (detJet021 b c d e U).2
    · simpa only [cutEdge029_3] using (detJet013 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut029 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA029 (point b c d e U)) (entriesH029 (point b c d e U)) (childD029 (point b c d e U)) (childJ029 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity029 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity029 (point b c d e U)).symm⟩
private theorem rows030 : ∀ i : Fin 3, suffixRows4 i.succ = suffixRows3 i := by decide +kernel
private theorem cols030_0 : ∀ l : Fin 3, minorCols030 ((0 : Fin 4).succAbove l) = minorCols028 l := by
  decide +kernel
private theorem cutEdge030_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut030 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut028 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows030 i) (cols030_0 l)
private theorem cols030_1 : ∀ l : Fin 3, minorCols030 ((1 : Fin 4).succAbove l) = minorCols026 l := by
  decide +kernel
private theorem cutEdge030_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut030 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut026 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows030 i) (cols030_1 l)
private theorem cols030_2 : ∀ l : Fin 3, minorCols030 ((2 : Fin 4).succAbove l) = minorCols022 l := by
  decide +kernel
private theorem cutEdge030_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut030 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut022 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows030 i) (cols030_2 l)
private theorem cols030_3 : ∀ l : Fin 3, minorCols030 ((3 : Fin 4).succAbove l) = minorCols014 l := by
  decide +kernel
private theorem cutEdge030_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut030 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut014 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows030 i) (cols030_3 l)
theorem detJet030 (b c d e U : ℂ) :
    (cut030 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D030 ∧
    HasDerivAt (fun T : ℂ => (cut030 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J030) 0 := by
  have he : ∀ j : Fin 4, cut030 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA030 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut030 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA030 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 4
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut030 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH030 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut030 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH030 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 4
  have hd : ∀ j : Fin 4, ((cut030 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD030 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut030 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD030 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge030_0] using (detJet028 b c d e U).1
    · simpa only [cutEdge030_1] using (detJet026 b c d e U).1
    · simpa only [cutEdge030_2] using (detJet022 b c d e U).1
    · simpa only [cutEdge030_3] using (detJet014 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut030 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ030 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut030 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ030 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge030_0] using (detJet028 b c d e U).2
    · simpa only [cutEdge030_1] using (detJet026 b c d e U).2
    · simpa only [cutEdge030_2] using (detJet022 b c d e U).2
    · simpa only [cutEdge030_3] using (detJet014 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut030 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA030 (point b c d e U)) (entriesH030 (point b c d e U)) (childD030 (point b c d e U)) (childJ030 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity030 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity030 (point b c d e U)).symm⟩
private theorem rows039 : ∀ i : Fin 3, suffixRows4 i.succ = suffixRows3 i := by decide +kernel
private theorem cols039_0 : ∀ l : Fin 3, minorCols039 ((0 : Fin 4).succAbove l) = minorCols038 l := by
  decide +kernel
private theorem cutEdge039_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut039 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut038 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows039 i) (cols039_0 l)
private theorem cols039_1 : ∀ l : Fin 3, minorCols039 ((1 : Fin 4).succAbove l) = minorCols037 l := by
  decide +kernel
private theorem cutEdge039_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut039 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut037 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows039 i) (cols039_1 l)
private theorem cols039_2 : ∀ l : Fin 3, minorCols039 ((2 : Fin 4).succAbove l) = minorCols035 l := by
  decide +kernel
private theorem cutEdge039_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut039 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut035 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows039 i) (cols039_2 l)
private theorem cols039_3 : ∀ l : Fin 3, minorCols039 ((3 : Fin 4).succAbove l) = minorCols007 l := by
  decide +kernel
private theorem cutEdge039_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut039 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut007 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows039 i) (cols039_3 l)
theorem detJet039 (b c d e U : ℂ) :
    (cut039 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D039 ∧
    HasDerivAt (fun T : ℂ => (cut039 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J039) 0 := by
  have he : ∀ j : Fin 4, cut039 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA039 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut039 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA039 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut039 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH039 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut039 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH039 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut039 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD039 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut039 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD039 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge039_0] using (detJet038 b c d e U).1
    · simpa only [cutEdge039_1] using (detJet037 b c d e U).1
    · simpa only [cutEdge039_2] using (detJet035 b c d e U).1
    · simpa only [cutEdge039_3] using (detJet007 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut039 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ039 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut039 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ039 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge039_0] using (detJet038 b c d e U).2
    · simpa only [cutEdge039_1] using (detJet037 b c d e U).2
    · simpa only [cutEdge039_2] using (detJet035 b c d e U).2
    · simpa only [cutEdge039_3] using (detJet007 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut039 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA039 (point b c d e U)) (entriesH039 (point b c d e U)) (childD039 (point b c d e U)) (childJ039 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity039 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity039 (point b c d e U)).symm⟩
private theorem rows043 : ∀ i : Fin 3, suffixRows4 i.succ = suffixRows3 i := by decide +kernel
private theorem cols043_0 : ∀ l : Fin 3, minorCols043 ((0 : Fin 4).succAbove l) = minorCols042 l := by
  decide +kernel
private theorem cutEdge043_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut043 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut042 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows043 i) (cols043_0 l)
private theorem cols043_1 : ∀ l : Fin 3, minorCols043 ((1 : Fin 4).succAbove l) = minorCols041 l := by
  decide +kernel
private theorem cutEdge043_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut043 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut041 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows043 i) (cols043_1 l)
private theorem cols043_2 : ∀ l : Fin 3, minorCols043 ((2 : Fin 4).succAbove l) = minorCols035 l := by
  decide +kernel
private theorem cutEdge043_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut043 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut035 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows043 i) (cols043_2 l)
private theorem cols043_3 : ∀ l : Fin 3, minorCols043 ((3 : Fin 4).succAbove l) = minorCols011 l := by
  decide +kernel
private theorem cutEdge043_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut043 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut011 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows043 i) (cols043_3 l)
theorem detJet043 (b c d e U : ℂ) :
    (cut043 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D043 ∧
    HasDerivAt (fun T : ℂ => (cut043 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J043) 0 := by
  have he : ∀ j : Fin 4, cut043 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA043 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut043 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA043 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut043 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH043 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut043 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH043 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut043 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD043 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut043 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD043 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge043_0] using (detJet042 b c d e U).1
    · simpa only [cutEdge043_1] using (detJet041 b c d e U).1
    · simpa only [cutEdge043_2] using (detJet035 b c d e U).1
    · simpa only [cutEdge043_3] using (detJet011 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut043 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ043 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut043 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ043 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge043_0] using (detJet042 b c d e U).2
    · simpa only [cutEdge043_1] using (detJet041 b c d e U).2
    · simpa only [cutEdge043_2] using (detJet035 b c d e U).2
    · simpa only [cutEdge043_3] using (detJet011 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut043 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA043 (point b c d e U)) (entriesH043 (point b c d e U)) (childD043 (point b c d e U)) (childJ043 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity043 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity043 (point b c d e U)).symm⟩
end N6.Exceptional
