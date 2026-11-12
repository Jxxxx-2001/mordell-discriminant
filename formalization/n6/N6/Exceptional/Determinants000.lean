import N6.Exceptional.DeterminantsBase
import N6.Exceptional.Arithmetic000
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.Resultant6
private theorem rows001 : ∀ i : Fin 0, suffixRows1 i.succ = suffixRows0 i := by decide +kernel
private theorem cols001_0 : ∀ l : Fin 0, minorCols001 ((0 : Fin 1).succAbove l) = minorCols000 l := by
  decide +kernel
private theorem cutEdge001_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut001 A).submatrix Fin.succ (0 : Fin 1).succAbove = cut000 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows001 i) (cols001_0 l)
theorem detJet001 (b c d e U : ℂ) :
    (cut001 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D001 ∧
    HasDerivAt (fun T : ℂ => (cut001 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J001) 0 := by
  have he : ∀ j : Fin 1, cut001 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA001 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => cut001 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA001 (point b c d e U) j) ?_
    · exact presentation_entry_zero b c d e U 5 0
  have he' : ∀ j : Fin 1, HasDerivAt (fun T : ℂ => cut001 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH001 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => HasDerivAt (fun T : ℂ => cut001 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH001 (point b c d e U) j) 0) ?_
    · exact presentation_entry_hasDerivAt b c d e U 5 0
  have hd : ∀ j : Fin 1, ((cut001 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD001 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => ((cut001 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD001 (point b c d e U) j) ?_
    · simpa only [cutEdge001_0] using (detJet000 b c d e U).1
  have hd' : ∀ j : Fin 1, HasDerivAt (fun T : ℂ => ((cut001 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ001 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => HasDerivAt (fun T : ℂ => ((cut001 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ001 (point b c d e U) j) 0) ?_
    · simpa only [cutEdge001_0] using (detJet000 b c d e U).2
  have step := det_row_zero_jet (n := 0) (fun T : ℂ => cut001 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA001 (point b c d e U)) (entriesH001 (point b c d e U)) (childD001 (point b c d e U)) (childJ001 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity001 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity001 (point b c d e U)).symm⟩
private theorem rows002 : ∀ i : Fin 0, suffixRows1 i.succ = suffixRows0 i := by decide +kernel
private theorem cols002_0 : ∀ l : Fin 0, minorCols002 ((0 : Fin 1).succAbove l) = minorCols000 l := by
  decide +kernel
private theorem cutEdge002_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut002 A).submatrix Fin.succ (0 : Fin 1).succAbove = cut000 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows002 i) (cols002_0 l)
theorem detJet002 (b c d e U : ℂ) :
    (cut002 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D002 ∧
    HasDerivAt (fun T : ℂ => (cut002 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J002) 0 := by
  have he : ∀ j : Fin 1, cut002 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA002 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => cut002 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA002 (point b c d e U) j) ?_
    · exact presentation_entry_zero b c d e U 5 1
  have he' : ∀ j : Fin 1, HasDerivAt (fun T : ℂ => cut002 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH002 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => HasDerivAt (fun T : ℂ => cut002 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH002 (point b c d e U) j) 0) ?_
    · exact presentation_entry_hasDerivAt b c d e U 5 1
  have hd : ∀ j : Fin 1, ((cut002 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD002 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => ((cut002 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD002 (point b c d e U) j) ?_
    · simpa only [cutEdge002_0] using (detJet000 b c d e U).1
  have hd' : ∀ j : Fin 1, HasDerivAt (fun T : ℂ => ((cut002 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ002 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => HasDerivAt (fun T : ℂ => ((cut002 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ002 (point b c d e U) j) 0) ?_
    · simpa only [cutEdge002_0] using (detJet000 b c d e U).2
  have step := det_row_zero_jet (n := 0) (fun T : ℂ => cut002 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA002 (point b c d e U)) (entriesH002 (point b c d e U)) (childD002 (point b c d e U)) (childJ002 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity002 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity002 (point b c d e U)).symm⟩
private theorem rows004 : ∀ i : Fin 0, suffixRows1 i.succ = suffixRows0 i := by decide +kernel
private theorem cols004_0 : ∀ l : Fin 0, minorCols004 ((0 : Fin 1).succAbove l) = minorCols000 l := by
  decide +kernel
private theorem cutEdge004_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut004 A).submatrix Fin.succ (0 : Fin 1).succAbove = cut000 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows004 i) (cols004_0 l)
theorem detJet004 (b c d e U : ℂ) :
    (cut004 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D004 ∧
    HasDerivAt (fun T : ℂ => (cut004 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J004) 0 := by
  have he : ∀ j : Fin 1, cut004 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA004 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => cut004 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA004 (point b c d e U) j) ?_
    · exact presentation_entry_zero b c d e U 5 2
  have he' : ∀ j : Fin 1, HasDerivAt (fun T : ℂ => cut004 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH004 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => HasDerivAt (fun T : ℂ => cut004 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH004 (point b c d e U) j) 0) ?_
    · exact presentation_entry_hasDerivAt b c d e U 5 2
  have hd : ∀ j : Fin 1, ((cut004 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD004 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => ((cut004 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD004 (point b c d e U) j) ?_
    · simpa only [cutEdge004_0] using (detJet000 b c d e U).1
  have hd' : ∀ j : Fin 1, HasDerivAt (fun T : ℂ => ((cut004 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ004 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => HasDerivAt (fun T : ℂ => ((cut004 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ004 (point b c d e U) j) 0) ?_
    · simpa only [cutEdge004_0] using (detJet000 b c d e U).2
  have step := det_row_zero_jet (n := 0) (fun T : ℂ => cut004 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA004 (point b c d e U)) (entriesH004 (point b c d e U)) (childD004 (point b c d e U)) (childJ004 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity004 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity004 (point b c d e U)).symm⟩
private theorem rows008 : ∀ i : Fin 0, suffixRows1 i.succ = suffixRows0 i := by decide +kernel
private theorem cols008_0 : ∀ l : Fin 0, minorCols008 ((0 : Fin 1).succAbove l) = minorCols000 l := by
  decide +kernel
private theorem cutEdge008_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut008 A).submatrix Fin.succ (0 : Fin 1).succAbove = cut000 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows008 i) (cols008_0 l)
theorem detJet008 (b c d e U : ℂ) :
    (cut008 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D008 ∧
    HasDerivAt (fun T : ℂ => (cut008 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J008) 0 := by
  have he : ∀ j : Fin 1, cut008 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA008 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => cut008 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA008 (point b c d e U) j) ?_
    · exact presentation_entry_zero b c d e U 5 3
  have he' : ∀ j : Fin 1, HasDerivAt (fun T : ℂ => cut008 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH008 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => HasDerivAt (fun T : ℂ => cut008 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH008 (point b c d e U) j) 0) ?_
    · exact presentation_entry_hasDerivAt b c d e U 5 3
  have hd : ∀ j : Fin 1, ((cut008 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD008 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => ((cut008 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD008 (point b c d e U) j) ?_
    · simpa only [cutEdge008_0] using (detJet000 b c d e U).1
  have hd' : ∀ j : Fin 1, HasDerivAt (fun T : ℂ => ((cut008 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ008 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => HasDerivAt (fun T : ℂ => ((cut008 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ008 (point b c d e U) j) 0) ?_
    · simpa only [cutEdge008_0] using (detJet000 b c d e U).2
  have step := det_row_zero_jet (n := 0) (fun T : ℂ => cut008 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA008 (point b c d e U)) (entriesH008 (point b c d e U)) (childD008 (point b c d e U)) (childJ008 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity008 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity008 (point b c d e U)).symm⟩
private theorem rows016 : ∀ i : Fin 0, suffixRows1 i.succ = suffixRows0 i := by decide +kernel
private theorem cols016_0 : ∀ l : Fin 0, minorCols016 ((0 : Fin 1).succAbove l) = minorCols000 l := by
  decide +kernel
private theorem cutEdge016_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut016 A).submatrix Fin.succ (0 : Fin 1).succAbove = cut000 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows016 i) (cols016_0 l)
theorem detJet016 (b c d e U : ℂ) :
    (cut016 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D016 ∧
    HasDerivAt (fun T : ℂ => (cut016 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J016) 0 := by
  have he : ∀ j : Fin 1, cut016 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA016 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => cut016 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA016 (point b c d e U) j) ?_
    · exact presentation_entry_zero b c d e U 5 4
  have he' : ∀ j : Fin 1, HasDerivAt (fun T : ℂ => cut016 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH016 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => HasDerivAt (fun T : ℂ => cut016 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH016 (point b c d e U) j) 0) ?_
    · exact presentation_entry_hasDerivAt b c d e U 5 4
  have hd : ∀ j : Fin 1, ((cut016 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD016 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => ((cut016 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD016 (point b c d e U) j) ?_
    · simpa only [cutEdge016_0] using (detJet000 b c d e U).1
  have hd' : ∀ j : Fin 1, HasDerivAt (fun T : ℂ => ((cut016 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ016 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => HasDerivAt (fun T : ℂ => ((cut016 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ016 (point b c d e U) j) 0) ?_
    · simpa only [cutEdge016_0] using (detJet000 b c d e U).2
  have step := det_row_zero_jet (n := 0) (fun T : ℂ => cut016 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA016 (point b c d e U)) (entriesH016 (point b c d e U)) (childD016 (point b c d e U)) (childJ016 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity016 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity016 (point b c d e U)).symm⟩
private theorem rows032 : ∀ i : Fin 0, suffixRows1 i.succ = suffixRows0 i := by decide +kernel
private theorem cols032_0 : ∀ l : Fin 0, minorCols032 ((0 : Fin 1).succAbove l) = minorCols000 l := by
  decide +kernel
private theorem cutEdge032_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut032 A).submatrix Fin.succ (0 : Fin 1).succAbove = cut000 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows032 i) (cols032_0 l)
theorem detJet032 (b c d e U : ℂ) :
    (cut032 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D032 ∧
    HasDerivAt (fun T : ℂ => (cut032 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J032) 0 := by
  have he : ∀ j : Fin 1, cut032 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA032 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => cut032 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA032 (point b c d e U) j) ?_
    · exact presentation_entry_zero b c d e U 5 5
  have he' : ∀ j : Fin 1, HasDerivAt (fun T : ℂ => cut032 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH032 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => HasDerivAt (fun T : ℂ => cut032 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH032 (point b c d e U) j) 0) ?_
    · exact presentation_entry_hasDerivAt b c d e U 5 5
  have hd : ∀ j : Fin 1, ((cut032 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD032 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => ((cut032 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD032 (point b c d e U) j) ?_
    · simpa only [cutEdge032_0] using (detJet000 b c d e U).1
  have hd' : ∀ j : Fin 1, HasDerivAt (fun T : ℂ => ((cut032 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ032 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin1 (P := fun j => HasDerivAt (fun T : ℂ => ((cut032 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ032 (point b c d e U) j) 0) ?_
    · simpa only [cutEdge032_0] using (detJet000 b c d e U).2
  have step := det_row_zero_jet (n := 0) (fun T : ℂ => cut032 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA032 (point b c d e U)) (entriesH032 (point b c d e U)) (childD032 (point b c d e U)) (childJ032 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity032 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity032 (point b c d e U)).symm⟩
private theorem rows003 : ∀ i : Fin 1, suffixRows2 i.succ = suffixRows1 i := by decide +kernel
private theorem cols003_0 : ∀ l : Fin 1, minorCols003 ((0 : Fin 2).succAbove l) = minorCols002 l := by
  decide +kernel
private theorem cutEdge003_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut003 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut002 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows003 i) (cols003_0 l)
private theorem cols003_1 : ∀ l : Fin 1, minorCols003 ((1 : Fin 2).succAbove l) = minorCols001 l := by
  decide +kernel
private theorem cutEdge003_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut003 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut001 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows003 i) (cols003_1 l)
theorem detJet003 (b c d e U : ℂ) :
    (cut003 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D003 ∧
    HasDerivAt (fun T : ℂ => (cut003 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J003) 0 := by
  have he : ∀ j : Fin 2, cut003 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA003 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin2 (P := fun j => cut003 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA003 (point b c d e U) j) ?_ ?_
    · exact presentation_entry_zero b c d e U 4 0
    · exact presentation_entry_zero b c d e U 4 1
  have he' : ∀ j : Fin 2, HasDerivAt (fun T : ℂ => cut003 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH003 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin2 (P := fun j => HasDerivAt (fun T : ℂ => cut003 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH003 (point b c d e U) j) 0) ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 4 0
    · exact presentation_entry_hasDerivAt b c d e U 4 1
  have hd : ∀ j : Fin 2, ((cut003 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD003 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin2 (P := fun j => ((cut003 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD003 (point b c d e U) j) ?_ ?_
    · simpa only [cutEdge003_0] using (detJet002 b c d e U).1
    · simpa only [cutEdge003_1] using (detJet001 b c d e U).1
  have hd' : ∀ j : Fin 2, HasDerivAt (fun T : ℂ => ((cut003 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ003 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin2 (P := fun j => HasDerivAt (fun T : ℂ => ((cut003 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ003 (point b c d e U) j) 0) ?_ ?_
    · simpa only [cutEdge003_0] using (detJet002 b c d e U).2
    · simpa only [cutEdge003_1] using (detJet001 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut003 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA003 (point b c d e U)) (entriesH003 (point b c d e U)) (childD003 (point b c d e U)) (childJ003 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity003 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity003 (point b c d e U)).symm⟩
private theorem rows005 : ∀ i : Fin 1, suffixRows2 i.succ = suffixRows1 i := by decide +kernel
private theorem cols005_0 : ∀ l : Fin 1, minorCols005 ((0 : Fin 2).succAbove l) = minorCols004 l := by
  decide +kernel
private theorem cutEdge005_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut005 A).submatrix Fin.succ (0 : Fin 2).succAbove = cut004 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows005 i) (cols005_0 l)
private theorem cols005_1 : ∀ l : Fin 1, minorCols005 ((1 : Fin 2).succAbove l) = minorCols001 l := by
  decide +kernel
private theorem cutEdge005_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut005 A).submatrix Fin.succ (1 : Fin 2).succAbove = cut001 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows005 i) (cols005_1 l)
theorem detJet005 (b c d e U : ℂ) :
    (cut005 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D005 ∧
    HasDerivAt (fun T : ℂ => (cut005 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J005) 0 := by
  have he : ∀ j : Fin 2, cut005 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA005 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin2 (P := fun j => cut005 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA005 (point b c d e U) j) ?_ ?_
    · exact presentation_entry_zero b c d e U 4 0
    · exact presentation_entry_zero b c d e U 4 2
  have he' : ∀ j : Fin 2, HasDerivAt (fun T : ℂ => cut005 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH005 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin2 (P := fun j => HasDerivAt (fun T : ℂ => cut005 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH005 (point b c d e U) j) 0) ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 4 0
    · exact presentation_entry_hasDerivAt b c d e U 4 2
  have hd : ∀ j : Fin 2, ((cut005 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD005 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin2 (P := fun j => ((cut005 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD005 (point b c d e U) j) ?_ ?_
    · simpa only [cutEdge005_0] using (detJet004 b c d e U).1
    · simpa only [cutEdge005_1] using (detJet001 b c d e U).1
  have hd' : ∀ j : Fin 2, HasDerivAt (fun T : ℂ => ((cut005 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ005 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin2 (P := fun j => HasDerivAt (fun T : ℂ => ((cut005 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ005 (point b c d e U) j) 0) ?_ ?_
    · simpa only [cutEdge005_0] using (detJet004 b c d e U).2
    · simpa only [cutEdge005_1] using (detJet001 b c d e U).2
  have step := det_row_zero_jet (n := 1) (fun T : ℂ => cut005 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA005 (point b c d e U)) (entriesH005 (point b c d e U)) (childD005 (point b c d e U)) (childJ005 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity005 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity005 (point b c d e U)).symm⟩
end N6.Exceptional
