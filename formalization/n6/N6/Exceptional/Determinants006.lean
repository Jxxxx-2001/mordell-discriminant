import N6.Exceptional.Determinants005
import N6.Exceptional.Arithmetic006
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.Resultant6
private theorem rows045 : ∀ i : Fin 3, suffixRows4 i.succ = suffixRows3 i := by decide +kernel
private theorem cols045_0 : ∀ l : Fin 3, minorCols045 ((0 : Fin 4).succAbove l) = minorCols044 l := by
  decide +kernel
private theorem cutEdge045_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut045 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut044 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows045 i) (cols045_0 l)
private theorem cols045_1 : ∀ l : Fin 3, minorCols045 ((1 : Fin 4).succAbove l) = minorCols041 l := by
  decide +kernel
private theorem cutEdge045_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut045 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut041 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows045 i) (cols045_1 l)
private theorem cols045_2 : ∀ l : Fin 3, minorCols045 ((2 : Fin 4).succAbove l) = minorCols037 l := by
  decide +kernel
private theorem cutEdge045_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut045 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut037 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows045 i) (cols045_2 l)
private theorem cols045_3 : ∀ l : Fin 3, minorCols045 ((3 : Fin 4).succAbove l) = minorCols013 l := by
  decide +kernel
private theorem cutEdge045_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut045 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut013 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows045 i) (cols045_3 l)
theorem detJet045 (b c d e U : ℂ) :
    (cut045 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D045 ∧
    HasDerivAt (fun T : ℂ => (cut045 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J045) 0 := by
  have he : ∀ j : Fin 4, cut045 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA045 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut045 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA045 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut045 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH045 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut045 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH045 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut045 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD045 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut045 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD045 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge045_0] using (detJet044 b c d e U).1
    · simpa only [cutEdge045_1] using (detJet041 b c d e U).1
    · simpa only [cutEdge045_2] using (detJet037 b c d e U).1
    · simpa only [cutEdge045_3] using (detJet013 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut045 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ045 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut045 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ045 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge045_0] using (detJet044 b c d e U).2
    · simpa only [cutEdge045_1] using (detJet041 b c d e U).2
    · simpa only [cutEdge045_2] using (detJet037 b c d e U).2
    · simpa only [cutEdge045_3] using (detJet013 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut045 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA045 (point b c d e U)) (entriesH045 (point b c d e U)) (childD045 (point b c d e U)) (childJ045 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity045 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity045 (point b c d e U)).symm⟩
private theorem rows046 : ∀ i : Fin 3, suffixRows4 i.succ = suffixRows3 i := by decide +kernel
private theorem cols046_0 : ∀ l : Fin 3, minorCols046 ((0 : Fin 4).succAbove l) = minorCols044 l := by
  decide +kernel
private theorem cutEdge046_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut046 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut044 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows046 i) (cols046_0 l)
private theorem cols046_1 : ∀ l : Fin 3, minorCols046 ((1 : Fin 4).succAbove l) = minorCols042 l := by
  decide +kernel
private theorem cutEdge046_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut046 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut042 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows046 i) (cols046_1 l)
private theorem cols046_2 : ∀ l : Fin 3, minorCols046 ((2 : Fin 4).succAbove l) = minorCols038 l := by
  decide +kernel
private theorem cutEdge046_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut046 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut038 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows046 i) (cols046_2 l)
private theorem cols046_3 : ∀ l : Fin 3, minorCols046 ((3 : Fin 4).succAbove l) = minorCols014 l := by
  decide +kernel
private theorem cutEdge046_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut046 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut014 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows046 i) (cols046_3 l)
theorem detJet046 (b c d e U : ℂ) :
    (cut046 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D046 ∧
    HasDerivAt (fun T : ℂ => (cut046 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J046) 0 := by
  have he : ∀ j : Fin 4, cut046 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA046 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut046 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA046 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut046 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH046 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut046 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH046 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut046 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD046 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut046 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD046 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge046_0] using (detJet044 b c d e U).1
    · simpa only [cutEdge046_1] using (detJet042 b c d e U).1
    · simpa only [cutEdge046_2] using (detJet038 b c d e U).1
    · simpa only [cutEdge046_3] using (detJet014 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut046 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ046 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut046 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ046 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge046_0] using (detJet044 b c d e U).2
    · simpa only [cutEdge046_1] using (detJet042 b c d e U).2
    · simpa only [cutEdge046_2] using (detJet038 b c d e U).2
    · simpa only [cutEdge046_3] using (detJet014 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut046 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA046 (point b c d e U)) (entriesH046 (point b c d e U)) (childD046 (point b c d e U)) (childJ046 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity046 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity046 (point b c d e U)).symm⟩
private theorem rows051 : ∀ i : Fin 3, suffixRows4 i.succ = suffixRows3 i := by decide +kernel
private theorem cols051_0 : ∀ l : Fin 3, minorCols051 ((0 : Fin 4).succAbove l) = minorCols050 l := by
  decide +kernel
private theorem cutEdge051_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut051 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut050 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows051 i) (cols051_0 l)
private theorem cols051_1 : ∀ l : Fin 3, minorCols051 ((1 : Fin 4).succAbove l) = minorCols049 l := by
  decide +kernel
private theorem cutEdge051_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut051 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut049 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows051 i) (cols051_1 l)
private theorem cols051_2 : ∀ l : Fin 3, minorCols051 ((2 : Fin 4).succAbove l) = minorCols035 l := by
  decide +kernel
private theorem cutEdge051_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut051 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut035 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows051 i) (cols051_2 l)
private theorem cols051_3 : ∀ l : Fin 3, minorCols051 ((3 : Fin 4).succAbove l) = minorCols019 l := by
  decide +kernel
private theorem cutEdge051_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut051 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut019 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows051 i) (cols051_3 l)
theorem detJet051 (b c d e U : ℂ) :
    (cut051 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D051 ∧
    HasDerivAt (fun T : ℂ => (cut051 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J051) 0 := by
  have he : ∀ j : Fin 4, cut051 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA051 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut051 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA051 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 4
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut051 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH051 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut051 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH051 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 4
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut051 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD051 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut051 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD051 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge051_0] using (detJet050 b c d e U).1
    · simpa only [cutEdge051_1] using (detJet049 b c d e U).1
    · simpa only [cutEdge051_2] using (detJet035 b c d e U).1
    · simpa only [cutEdge051_3] using (detJet019 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut051 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ051 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut051 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ051 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge051_0] using (detJet050 b c d e U).2
    · simpa only [cutEdge051_1] using (detJet049 b c d e U).2
    · simpa only [cutEdge051_2] using (detJet035 b c d e U).2
    · simpa only [cutEdge051_3] using (detJet019 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut051 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA051 (point b c d e U)) (entriesH051 (point b c d e U)) (childD051 (point b c d e U)) (childJ051 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity051 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity051 (point b c d e U)).symm⟩
private theorem rows053 : ∀ i : Fin 3, suffixRows4 i.succ = suffixRows3 i := by decide +kernel
private theorem cols053_0 : ∀ l : Fin 3, minorCols053 ((0 : Fin 4).succAbove l) = minorCols052 l := by
  decide +kernel
private theorem cutEdge053_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut053 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut052 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows053 i) (cols053_0 l)
private theorem cols053_1 : ∀ l : Fin 3, minorCols053 ((1 : Fin 4).succAbove l) = minorCols049 l := by
  decide +kernel
private theorem cutEdge053_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut053 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut049 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows053 i) (cols053_1 l)
private theorem cols053_2 : ∀ l : Fin 3, minorCols053 ((2 : Fin 4).succAbove l) = minorCols037 l := by
  decide +kernel
private theorem cutEdge053_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut053 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut037 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows053 i) (cols053_2 l)
private theorem cols053_3 : ∀ l : Fin 3, minorCols053 ((3 : Fin 4).succAbove l) = minorCols021 l := by
  decide +kernel
private theorem cutEdge053_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut053 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut021 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows053 i) (cols053_3 l)
theorem detJet053 (b c d e U : ℂ) :
    (cut053 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D053 ∧
    HasDerivAt (fun T : ℂ => (cut053 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J053) 0 := by
  have he : ∀ j : Fin 4, cut053 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA053 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut053 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA053 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 4
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut053 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH053 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut053 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH053 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 4
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut053 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD053 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut053 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD053 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge053_0] using (detJet052 b c d e U).1
    · simpa only [cutEdge053_1] using (detJet049 b c d e U).1
    · simpa only [cutEdge053_2] using (detJet037 b c d e U).1
    · simpa only [cutEdge053_3] using (detJet021 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut053 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ053 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut053 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ053 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge053_0] using (detJet052 b c d e U).2
    · simpa only [cutEdge053_1] using (detJet049 b c d e U).2
    · simpa only [cutEdge053_2] using (detJet037 b c d e U).2
    · simpa only [cutEdge053_3] using (detJet021 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut053 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA053 (point b c d e U)) (entriesH053 (point b c d e U)) (childD053 (point b c d e U)) (childJ053 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity053 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity053 (point b c d e U)).symm⟩
private theorem rows054 : ∀ i : Fin 3, suffixRows4 i.succ = suffixRows3 i := by decide +kernel
private theorem cols054_0 : ∀ l : Fin 3, minorCols054 ((0 : Fin 4).succAbove l) = minorCols052 l := by
  decide +kernel
private theorem cutEdge054_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut054 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut052 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows054 i) (cols054_0 l)
private theorem cols054_1 : ∀ l : Fin 3, minorCols054 ((1 : Fin 4).succAbove l) = minorCols050 l := by
  decide +kernel
private theorem cutEdge054_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut054 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut050 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows054 i) (cols054_1 l)
private theorem cols054_2 : ∀ l : Fin 3, minorCols054 ((2 : Fin 4).succAbove l) = minorCols038 l := by
  decide +kernel
private theorem cutEdge054_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut054 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut038 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows054 i) (cols054_2 l)
private theorem cols054_3 : ∀ l : Fin 3, minorCols054 ((3 : Fin 4).succAbove l) = minorCols022 l := by
  decide +kernel
private theorem cutEdge054_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut054 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut022 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows054 i) (cols054_3 l)
theorem detJet054 (b c d e U : ℂ) :
    (cut054 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D054 ∧
    HasDerivAt (fun T : ℂ => (cut054 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J054) 0 := by
  have he : ∀ j : Fin 4, cut054 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA054 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut054 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA054 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 4
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut054 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH054 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut054 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH054 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 4
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut054 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD054 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut054 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD054 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge054_0] using (detJet052 b c d e U).1
    · simpa only [cutEdge054_1] using (detJet050 b c d e U).1
    · simpa only [cutEdge054_2] using (detJet038 b c d e U).1
    · simpa only [cutEdge054_3] using (detJet022 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut054 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ054 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut054 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ054 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge054_0] using (detJet052 b c d e U).2
    · simpa only [cutEdge054_1] using (detJet050 b c d e U).2
    · simpa only [cutEdge054_2] using (detJet038 b c d e U).2
    · simpa only [cutEdge054_3] using (detJet022 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut054 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA054 (point b c d e U)) (entriesH054 (point b c d e U)) (childD054 (point b c d e U)) (childJ054 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity054 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity054 (point b c d e U)).symm⟩
private theorem rows057 : ∀ i : Fin 3, suffixRows4 i.succ = suffixRows3 i := by decide +kernel
private theorem cols057_0 : ∀ l : Fin 3, minorCols057 ((0 : Fin 4).succAbove l) = minorCols056 l := by
  decide +kernel
private theorem cutEdge057_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut057 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut056 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows057 i) (cols057_0 l)
private theorem cols057_1 : ∀ l : Fin 3, minorCols057 ((1 : Fin 4).succAbove l) = minorCols049 l := by
  decide +kernel
private theorem cutEdge057_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut057 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut049 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows057 i) (cols057_1 l)
private theorem cols057_2 : ∀ l : Fin 3, minorCols057 ((2 : Fin 4).succAbove l) = minorCols041 l := by
  decide +kernel
private theorem cutEdge057_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut057 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut041 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows057 i) (cols057_2 l)
private theorem cols057_3 : ∀ l : Fin 3, minorCols057 ((3 : Fin 4).succAbove l) = minorCols025 l := by
  decide +kernel
private theorem cutEdge057_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut057 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut025 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows057 i) (cols057_3 l)
theorem detJet057 (b c d e U : ℂ) :
    (cut057 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D057 ∧
    HasDerivAt (fun T : ℂ => (cut057 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J057) 0 := by
  have he : ∀ j : Fin 4, cut057 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA057 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut057 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA057 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 4
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut057 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH057 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut057 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH057 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 4
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut057 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD057 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut057 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD057 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge057_0] using (detJet056 b c d e U).1
    · simpa only [cutEdge057_1] using (detJet049 b c d e U).1
    · simpa only [cutEdge057_2] using (detJet041 b c d e U).1
    · simpa only [cutEdge057_3] using (detJet025 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut057 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ057 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut057 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ057 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge057_0] using (detJet056 b c d e U).2
    · simpa only [cutEdge057_1] using (detJet049 b c d e U).2
    · simpa only [cutEdge057_2] using (detJet041 b c d e U).2
    · simpa only [cutEdge057_3] using (detJet025 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut057 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA057 (point b c d e U)) (entriesH057 (point b c d e U)) (childD057 (point b c d e U)) (childJ057 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity057 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity057 (point b c d e U)).symm⟩
private theorem rows058 : ∀ i : Fin 3, suffixRows4 i.succ = suffixRows3 i := by decide +kernel
private theorem cols058_0 : ∀ l : Fin 3, minorCols058 ((0 : Fin 4).succAbove l) = minorCols056 l := by
  decide +kernel
private theorem cutEdge058_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut058 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut056 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows058 i) (cols058_0 l)
private theorem cols058_1 : ∀ l : Fin 3, minorCols058 ((1 : Fin 4).succAbove l) = minorCols050 l := by
  decide +kernel
private theorem cutEdge058_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut058 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut050 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows058 i) (cols058_1 l)
private theorem cols058_2 : ∀ l : Fin 3, minorCols058 ((2 : Fin 4).succAbove l) = minorCols042 l := by
  decide +kernel
private theorem cutEdge058_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut058 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut042 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows058 i) (cols058_2 l)
private theorem cols058_3 : ∀ l : Fin 3, minorCols058 ((3 : Fin 4).succAbove l) = minorCols026 l := by
  decide +kernel
private theorem cutEdge058_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut058 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut026 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows058 i) (cols058_3 l)
theorem detJet058 (b c d e U : ℂ) :
    (cut058 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D058 ∧
    HasDerivAt (fun T : ℂ => (cut058 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J058) 0 := by
  have he : ∀ j : Fin 4, cut058 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA058 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut058 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA058 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 4
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut058 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH058 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut058 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH058 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 4
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut058 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD058 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut058 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD058 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge058_0] using (detJet056 b c d e U).1
    · simpa only [cutEdge058_1] using (detJet050 b c d e U).1
    · simpa only [cutEdge058_2] using (detJet042 b c d e U).1
    · simpa only [cutEdge058_3] using (detJet026 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut058 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ058 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut058 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ058 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge058_0] using (detJet056 b c d e U).2
    · simpa only [cutEdge058_1] using (detJet050 b c d e U).2
    · simpa only [cutEdge058_2] using (detJet042 b c d e U).2
    · simpa only [cutEdge058_3] using (detJet026 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut058 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA058 (point b c d e U)) (entriesH058 (point b c d e U)) (childD058 (point b c d e U)) (childJ058 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity058 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity058 (point b c d e U)).symm⟩
private theorem rows060 : ∀ i : Fin 3, suffixRows4 i.succ = suffixRows3 i := by decide +kernel
private theorem cols060_0 : ∀ l : Fin 3, minorCols060 ((0 : Fin 4).succAbove l) = minorCols056 l := by
  decide +kernel
private theorem cutEdge060_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut060 A).submatrix Fin.succ (0 : Fin 4).succAbove = cut056 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows060 i) (cols060_0 l)
private theorem cols060_1 : ∀ l : Fin 3, minorCols060 ((1 : Fin 4).succAbove l) = minorCols052 l := by
  decide +kernel
private theorem cutEdge060_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut060 A).submatrix Fin.succ (1 : Fin 4).succAbove = cut052 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows060 i) (cols060_1 l)
private theorem cols060_2 : ∀ l : Fin 3, minorCols060 ((2 : Fin 4).succAbove l) = minorCols044 l := by
  decide +kernel
private theorem cutEdge060_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut060 A).submatrix Fin.succ (2 : Fin 4).succAbove = cut044 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows060 i) (cols060_2 l)
private theorem cols060_3 : ∀ l : Fin 3, minorCols060 ((3 : Fin 4).succAbove l) = minorCols028 l := by
  decide +kernel
private theorem cutEdge060_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut060 A).submatrix Fin.succ (3 : Fin 4).succAbove = cut028 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows060 i) (cols060_3 l)
theorem detJet060 (b c d e U : ℂ) :
    (cut060 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D060 ∧
    HasDerivAt (fun T : ℂ => (cut060 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J060) 0 := by
  have he : ∀ j : Fin 4, cut060 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA060 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut060 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA060 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 4
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut060 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH060 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut060 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH060 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 4
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut060 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD060 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut060 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD060 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge060_0] using (detJet056 b c d e U).1
    · simpa only [cutEdge060_1] using (detJet052 b c d e U).1
    · simpa only [cutEdge060_2] using (detJet044 b c d e U).1
    · simpa only [cutEdge060_3] using (detJet028 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut060 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ060 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut060 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ060 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge060_0] using (detJet056 b c d e U).2
    · simpa only [cutEdge060_1] using (detJet052 b c d e U).2
    · simpa only [cutEdge060_2] using (detJet044 b c d e U).2
    · simpa only [cutEdge060_3] using (detJet028 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut060 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA060 (point b c d e U)) (entriesH060 (point b c d e U)) (childD060 (point b c d e U)) (childJ060 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity060 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity060 (point b c d e U)).symm⟩
end N6.Exceptional
