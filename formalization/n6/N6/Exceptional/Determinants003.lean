import N6.Exceptional.Determinants002
import N6.Exceptional.Arithmetic003
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.Resultant6
private theorem rows014 : ∀ i : Fin 2, suffixRows3 i.succ = suffixRows2 i := by decide +kernel
private theorem cols014_0 : ∀ l : Fin 2, minorCols014 ((0 : Fin 3).succAbove l) = minorCols012 l := by
  decide +kernel
private theorem cutEdge014_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut014 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut012 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows014 i) (cols014_0 l)
private theorem cols014_1 : ∀ l : Fin 2, minorCols014 ((1 : Fin 3).succAbove l) = minorCols010 l := by
  decide +kernel
private theorem cutEdge014_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut014 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut010 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows014 i) (cols014_1 l)
private theorem cols014_2 : ∀ l : Fin 2, minorCols014 ((2 : Fin 3).succAbove l) = minorCols006 l := by
  decide +kernel
private theorem cutEdge014_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut014 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut006 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows014 i) (cols014_2 l)
theorem detJet014 (b c d e U : ℂ) :
    (cut014 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D014 ∧
    HasDerivAt (fun T : ℂ => (cut014 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J014) 0 := by
  have he : ∀ j : Fin 3, cut014 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA014 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => cut014 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA014 (point b c d e U) j) ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 3 1
    · exact presentation_entry_zero b c d e U 3 2
    · exact presentation_entry_zero b c d e U 3 3
  have he' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => cut014 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH014 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => cut014 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH014 (point b c d e U) j) 0) ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 3 1
    · exact presentation_entry_hasDerivAt b c d e U 3 2
    · exact presentation_entry_hasDerivAt b c d e U 3 3
  have hd : ∀ j : Fin 3, ((cut014 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD014 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => ((cut014 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD014 (point b c d e U) j) ?_ ?_ ?_
    · simpa only [cutEdge014_0] using (detJet012 b c d e U).1
    · simpa only [cutEdge014_1] using (detJet010 b c d e U).1
    · simpa only [cutEdge014_2] using (detJet006 b c d e U).1
  have hd' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => ((cut014 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ014 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => ((cut014 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ014 (point b c d e U) j) 0) ?_ ?_ ?_
    · simpa only [cutEdge014_0] using (detJet012 b c d e U).2
    · simpa only [cutEdge014_1] using (detJet010 b c d e U).2
    · simpa only [cutEdge014_2] using (detJet006 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut014 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA014 (point b c d e U)) (entriesH014 (point b c d e U)) (childD014 (point b c d e U)) (childJ014 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity014 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity014 (point b c d e U)).symm⟩
private theorem rows019 : ∀ i : Fin 2, suffixRows3 i.succ = suffixRows2 i := by decide +kernel
private theorem cols019_0 : ∀ l : Fin 2, minorCols019 ((0 : Fin 3).succAbove l) = minorCols018 l := by
  decide +kernel
private theorem cutEdge019_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut019 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut018 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows019 i) (cols019_0 l)
private theorem cols019_1 : ∀ l : Fin 2, minorCols019 ((1 : Fin 3).succAbove l) = minorCols017 l := by
  decide +kernel
private theorem cutEdge019_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut019 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut017 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows019 i) (cols019_1 l)
private theorem cols019_2 : ∀ l : Fin 2, minorCols019 ((2 : Fin 3).succAbove l) = minorCols003 l := by
  decide +kernel
private theorem cutEdge019_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut019 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut003 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows019 i) (cols019_2 l)
theorem detJet019 (b c d e U : ℂ) :
    (cut019 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D019 ∧
    HasDerivAt (fun T : ℂ => (cut019 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J019) 0 := by
  have he : ∀ j : Fin 3, cut019 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA019 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => cut019 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA019 (point b c d e U) j) ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 3 0
    · exact presentation_entry_zero b c d e U 3 1
    · exact presentation_entry_zero b c d e U 3 4
  have he' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => cut019 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH019 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => cut019 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH019 (point b c d e U) j) 0) ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 3 0
    · exact presentation_entry_hasDerivAt b c d e U 3 1
    · exact presentation_entry_hasDerivAt b c d e U 3 4
  have hd : ∀ j : Fin 3, ((cut019 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD019 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => ((cut019 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD019 (point b c d e U) j) ?_ ?_ ?_
    · simpa only [cutEdge019_0] using (detJet018 b c d e U).1
    · simpa only [cutEdge019_1] using (detJet017 b c d e U).1
    · simpa only [cutEdge019_2] using (detJet003 b c d e U).1
  have hd' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => ((cut019 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ019 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => ((cut019 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ019 (point b c d e U) j) 0) ?_ ?_ ?_
    · simpa only [cutEdge019_0] using (detJet018 b c d e U).2
    · simpa only [cutEdge019_1] using (detJet017 b c d e U).2
    · simpa only [cutEdge019_2] using (detJet003 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut019 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA019 (point b c d e U)) (entriesH019 (point b c d e U)) (childD019 (point b c d e U)) (childJ019 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity019 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity019 (point b c d e U)).symm⟩
private theorem rows021 : ∀ i : Fin 2, suffixRows3 i.succ = suffixRows2 i := by decide +kernel
private theorem cols021_0 : ∀ l : Fin 2, minorCols021 ((0 : Fin 3).succAbove l) = minorCols020 l := by
  decide +kernel
private theorem cutEdge021_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut021 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut020 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows021 i) (cols021_0 l)
private theorem cols021_1 : ∀ l : Fin 2, minorCols021 ((1 : Fin 3).succAbove l) = minorCols017 l := by
  decide +kernel
private theorem cutEdge021_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut021 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut017 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows021 i) (cols021_1 l)
private theorem cols021_2 : ∀ l : Fin 2, minorCols021 ((2 : Fin 3).succAbove l) = minorCols005 l := by
  decide +kernel
private theorem cutEdge021_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut021 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut005 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows021 i) (cols021_2 l)
theorem detJet021 (b c d e U : ℂ) :
    (cut021 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D021 ∧
    HasDerivAt (fun T : ℂ => (cut021 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J021) 0 := by
  have he : ∀ j : Fin 3, cut021 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA021 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => cut021 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA021 (point b c d e U) j) ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 3 0
    · exact presentation_entry_zero b c d e U 3 2
    · exact presentation_entry_zero b c d e U 3 4
  have he' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => cut021 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH021 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => cut021 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH021 (point b c d e U) j) 0) ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 3 0
    · exact presentation_entry_hasDerivAt b c d e U 3 2
    · exact presentation_entry_hasDerivAt b c d e U 3 4
  have hd : ∀ j : Fin 3, ((cut021 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD021 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => ((cut021 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD021 (point b c d e U) j) ?_ ?_ ?_
    · simpa only [cutEdge021_0] using (detJet020 b c d e U).1
    · simpa only [cutEdge021_1] using (detJet017 b c d e U).1
    · simpa only [cutEdge021_2] using (detJet005 b c d e U).1
  have hd' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => ((cut021 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ021 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => ((cut021 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ021 (point b c d e U) j) 0) ?_ ?_ ?_
    · simpa only [cutEdge021_0] using (detJet020 b c d e U).2
    · simpa only [cutEdge021_1] using (detJet017 b c d e U).2
    · simpa only [cutEdge021_2] using (detJet005 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut021 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA021 (point b c d e U)) (entriesH021 (point b c d e U)) (childD021 (point b c d e U)) (childJ021 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity021 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity021 (point b c d e U)).symm⟩
private theorem rows022 : ∀ i : Fin 2, suffixRows3 i.succ = suffixRows2 i := by decide +kernel
private theorem cols022_0 : ∀ l : Fin 2, minorCols022 ((0 : Fin 3).succAbove l) = minorCols020 l := by
  decide +kernel
private theorem cutEdge022_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut022 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut020 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows022 i) (cols022_0 l)
private theorem cols022_1 : ∀ l : Fin 2, minorCols022 ((1 : Fin 3).succAbove l) = minorCols018 l := by
  decide +kernel
private theorem cutEdge022_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut022 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut018 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows022 i) (cols022_1 l)
private theorem cols022_2 : ∀ l : Fin 2, minorCols022 ((2 : Fin 3).succAbove l) = minorCols006 l := by
  decide +kernel
private theorem cutEdge022_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut022 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut006 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows022 i) (cols022_2 l)
theorem detJet022 (b c d e U : ℂ) :
    (cut022 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D022 ∧
    HasDerivAt (fun T : ℂ => (cut022 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J022) 0 := by
  have he : ∀ j : Fin 3, cut022 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA022 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => cut022 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA022 (point b c d e U) j) ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 3 1
    · exact presentation_entry_zero b c d e U 3 2
    · exact presentation_entry_zero b c d e U 3 4
  have he' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => cut022 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH022 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => cut022 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH022 (point b c d e U) j) 0) ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 3 1
    · exact presentation_entry_hasDerivAt b c d e U 3 2
    · exact presentation_entry_hasDerivAt b c d e U 3 4
  have hd : ∀ j : Fin 3, ((cut022 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD022 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => ((cut022 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD022 (point b c d e U) j) ?_ ?_ ?_
    · simpa only [cutEdge022_0] using (detJet020 b c d e U).1
    · simpa only [cutEdge022_1] using (detJet018 b c d e U).1
    · simpa only [cutEdge022_2] using (detJet006 b c d e U).1
  have hd' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => ((cut022 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ022 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => ((cut022 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ022 (point b c d e U) j) 0) ?_ ?_ ?_
    · simpa only [cutEdge022_0] using (detJet020 b c d e U).2
    · simpa only [cutEdge022_1] using (detJet018 b c d e U).2
    · simpa only [cutEdge022_2] using (detJet006 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut022 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA022 (point b c d e U)) (entriesH022 (point b c d e U)) (childD022 (point b c d e U)) (childJ022 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity022 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity022 (point b c d e U)).symm⟩
private theorem rows025 : ∀ i : Fin 2, suffixRows3 i.succ = suffixRows2 i := by decide +kernel
private theorem cols025_0 : ∀ l : Fin 2, minorCols025 ((0 : Fin 3).succAbove l) = minorCols024 l := by
  decide +kernel
private theorem cutEdge025_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut025 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut024 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows025 i) (cols025_0 l)
private theorem cols025_1 : ∀ l : Fin 2, minorCols025 ((1 : Fin 3).succAbove l) = minorCols017 l := by
  decide +kernel
private theorem cutEdge025_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut025 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut017 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows025 i) (cols025_1 l)
private theorem cols025_2 : ∀ l : Fin 2, minorCols025 ((2 : Fin 3).succAbove l) = minorCols009 l := by
  decide +kernel
private theorem cutEdge025_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut025 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut009 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows025 i) (cols025_2 l)
theorem detJet025 (b c d e U : ℂ) :
    (cut025 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D025 ∧
    HasDerivAt (fun T : ℂ => (cut025 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J025) 0 := by
  have he : ∀ j : Fin 3, cut025 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA025 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => cut025 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA025 (point b c d e U) j) ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 3 0
    · exact presentation_entry_zero b c d e U 3 3
    · exact presentation_entry_zero b c d e U 3 4
  have he' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => cut025 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH025 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => cut025 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH025 (point b c d e U) j) 0) ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 3 0
    · exact presentation_entry_hasDerivAt b c d e U 3 3
    · exact presentation_entry_hasDerivAt b c d e U 3 4
  have hd : ∀ j : Fin 3, ((cut025 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD025 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => ((cut025 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD025 (point b c d e U) j) ?_ ?_ ?_
    · simpa only [cutEdge025_0] using (detJet024 b c d e U).1
    · simpa only [cutEdge025_1] using (detJet017 b c d e U).1
    · simpa only [cutEdge025_2] using (detJet009 b c d e U).1
  have hd' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => ((cut025 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ025 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => ((cut025 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ025 (point b c d e U) j) 0) ?_ ?_ ?_
    · simpa only [cutEdge025_0] using (detJet024 b c d e U).2
    · simpa only [cutEdge025_1] using (detJet017 b c d e U).2
    · simpa only [cutEdge025_2] using (detJet009 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut025 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA025 (point b c d e U)) (entriesH025 (point b c d e U)) (childD025 (point b c d e U)) (childJ025 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity025 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity025 (point b c d e U)).symm⟩
private theorem rows026 : ∀ i : Fin 2, suffixRows3 i.succ = suffixRows2 i := by decide +kernel
private theorem cols026_0 : ∀ l : Fin 2, minorCols026 ((0 : Fin 3).succAbove l) = minorCols024 l := by
  decide +kernel
private theorem cutEdge026_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut026 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut024 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows026 i) (cols026_0 l)
private theorem cols026_1 : ∀ l : Fin 2, minorCols026 ((1 : Fin 3).succAbove l) = minorCols018 l := by
  decide +kernel
private theorem cutEdge026_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut026 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut018 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows026 i) (cols026_1 l)
private theorem cols026_2 : ∀ l : Fin 2, minorCols026 ((2 : Fin 3).succAbove l) = minorCols010 l := by
  decide +kernel
private theorem cutEdge026_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut026 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut010 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows026 i) (cols026_2 l)
theorem detJet026 (b c d e U : ℂ) :
    (cut026 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D026 ∧
    HasDerivAt (fun T : ℂ => (cut026 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J026) 0 := by
  have he : ∀ j : Fin 3, cut026 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA026 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => cut026 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA026 (point b c d e U) j) ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 3 1
    · exact presentation_entry_zero b c d e U 3 3
    · exact presentation_entry_zero b c d e U 3 4
  have he' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => cut026 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH026 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => cut026 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH026 (point b c d e U) j) 0) ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 3 1
    · exact presentation_entry_hasDerivAt b c d e U 3 3
    · exact presentation_entry_hasDerivAt b c d e U 3 4
  have hd : ∀ j : Fin 3, ((cut026 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD026 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => ((cut026 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD026 (point b c d e U) j) ?_ ?_ ?_
    · simpa only [cutEdge026_0] using (detJet024 b c d e U).1
    · simpa only [cutEdge026_1] using (detJet018 b c d e U).1
    · simpa only [cutEdge026_2] using (detJet010 b c d e U).1
  have hd' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => ((cut026 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ026 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => ((cut026 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ026 (point b c d e U) j) 0) ?_ ?_ ?_
    · simpa only [cutEdge026_0] using (detJet024 b c d e U).2
    · simpa only [cutEdge026_1] using (detJet018 b c d e U).2
    · simpa only [cutEdge026_2] using (detJet010 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut026 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA026 (point b c d e U)) (entriesH026 (point b c d e U)) (childD026 (point b c d e U)) (childJ026 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity026 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity026 (point b c d e U)).symm⟩
private theorem rows028 : ∀ i : Fin 2, suffixRows3 i.succ = suffixRows2 i := by decide +kernel
private theorem cols028_0 : ∀ l : Fin 2, minorCols028 ((0 : Fin 3).succAbove l) = minorCols024 l := by
  decide +kernel
private theorem cutEdge028_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut028 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut024 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows028 i) (cols028_0 l)
private theorem cols028_1 : ∀ l : Fin 2, minorCols028 ((1 : Fin 3).succAbove l) = minorCols020 l := by
  decide +kernel
private theorem cutEdge028_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut028 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut020 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows028 i) (cols028_1 l)
private theorem cols028_2 : ∀ l : Fin 2, minorCols028 ((2 : Fin 3).succAbove l) = minorCols012 l := by
  decide +kernel
private theorem cutEdge028_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut028 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut012 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows028 i) (cols028_2 l)
theorem detJet028 (b c d e U : ℂ) :
    (cut028 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D028 ∧
    HasDerivAt (fun T : ℂ => (cut028 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J028) 0 := by
  have he : ∀ j : Fin 3, cut028 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA028 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => cut028 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA028 (point b c d e U) j) ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 3 2
    · exact presentation_entry_zero b c d e U 3 3
    · exact presentation_entry_zero b c d e U 3 4
  have he' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => cut028 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH028 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => cut028 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH028 (point b c d e U) j) 0) ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 3 2
    · exact presentation_entry_hasDerivAt b c d e U 3 3
    · exact presentation_entry_hasDerivAt b c d e U 3 4
  have hd : ∀ j : Fin 3, ((cut028 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD028 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => ((cut028 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD028 (point b c d e U) j) ?_ ?_ ?_
    · simpa only [cutEdge028_0] using (detJet024 b c d e U).1
    · simpa only [cutEdge028_1] using (detJet020 b c d e U).1
    · simpa only [cutEdge028_2] using (detJet012 b c d e U).1
  have hd' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => ((cut028 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ028 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => ((cut028 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ028 (point b c d e U) j) 0) ?_ ?_ ?_
    · simpa only [cutEdge028_0] using (detJet024 b c d e U).2
    · simpa only [cutEdge028_1] using (detJet020 b c d e U).2
    · simpa only [cutEdge028_2] using (detJet012 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut028 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA028 (point b c d e U)) (entriesH028 (point b c d e U)) (childD028 (point b c d e U)) (childJ028 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity028 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity028 (point b c d e U)).symm⟩
private theorem rows035 : ∀ i : Fin 2, suffixRows3 i.succ = suffixRows2 i := by decide +kernel
private theorem cols035_0 : ∀ l : Fin 2, minorCols035 ((0 : Fin 3).succAbove l) = minorCols034 l := by
  decide +kernel
private theorem cutEdge035_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut035 A).submatrix Fin.succ (0 : Fin 3).succAbove = cut034 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows035 i) (cols035_0 l)
private theorem cols035_1 : ∀ l : Fin 2, minorCols035 ((1 : Fin 3).succAbove l) = minorCols033 l := by
  decide +kernel
private theorem cutEdge035_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut035 A).submatrix Fin.succ (1 : Fin 3).succAbove = cut033 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows035 i) (cols035_1 l)
private theorem cols035_2 : ∀ l : Fin 2, minorCols035 ((2 : Fin 3).succAbove l) = minorCols003 l := by
  decide +kernel
private theorem cutEdge035_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut035 A).submatrix Fin.succ (2 : Fin 3).succAbove = cut003 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows035 i) (cols035_2 l)
theorem detJet035 (b c d e U : ℂ) :
    (cut035 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D035 ∧
    HasDerivAt (fun T : ℂ => (cut035 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J035) 0 := by
  have he : ∀ j : Fin 3, cut035 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA035 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => cut035 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA035 (point b c d e U) j) ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 3 0
    · exact presentation_entry_zero b c d e U 3 1
    · exact presentation_entry_zero b c d e U 3 5
  have he' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => cut035 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH035 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => cut035 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH035 (point b c d e U) j) 0) ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 3 0
    · exact presentation_entry_hasDerivAt b c d e U 3 1
    · exact presentation_entry_hasDerivAt b c d e U 3 5
  have hd : ∀ j : Fin 3, ((cut035 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD035 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => ((cut035 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD035 (point b c d e U) j) ?_ ?_ ?_
    · simpa only [cutEdge035_0] using (detJet034 b c d e U).1
    · simpa only [cutEdge035_1] using (detJet033 b c d e U).1
    · simpa only [cutEdge035_2] using (detJet003 b c d e U).1
  have hd' : ∀ j : Fin 3, HasDerivAt (fun T : ℂ => ((cut035 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ035 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin3 (P := fun j => HasDerivAt (fun T : ℂ => ((cut035 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ035 (point b c d e U) j) 0) ?_ ?_ ?_
    · simpa only [cutEdge035_0] using (detJet034 b c d e U).2
    · simpa only [cutEdge035_1] using (detJet033 b c d e U).2
    · simpa only [cutEdge035_2] using (detJet003 b c d e U).2
  have step := det_row_zero_jet (n := 2) (fun T : ℂ => cut035 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA035 (point b c d e U)) (entriesH035 (point b c d e U)) (childD035 (point b c d e U)) (childJ035 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity035 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity035 (point b c d e U)).symm⟩
end N6.Exceptional
