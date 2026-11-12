import N6.ResultantMinors.Determinants006_07
import N6.ResultantMinors.Arithmetic007
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem rows031 : ∀ i : Fin 4, suffixRows5 i.succ = suffixRows4 i := by decide +kernel
private theorem cols031_0 : ∀ l : Fin 4, minorCols031 ((0 : Fin 5).succAbove l) = minorCols030 l := by
  decide +kernel
private theorem cutEdge031_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut031 A).submatrix Fin.succ (0 : Fin 5).succAbove = cut030 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows031 i) (cols031_0 l)
private theorem cols031_1 : ∀ l : Fin 4, minorCols031 ((1 : Fin 5).succAbove l) = minorCols029 l := by
  decide +kernel
private theorem cutEdge031_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut031 A).submatrix Fin.succ (1 : Fin 5).succAbove = cut029 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows031 i) (cols031_1 l)
private theorem cols031_2 : ∀ l : Fin 4, minorCols031 ((2 : Fin 5).succAbove l) = minorCols027 l := by
  decide +kernel
private theorem cutEdge031_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut031 A).submatrix Fin.succ (2 : Fin 5).succAbove = cut027 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows031 i) (cols031_2 l)
private theorem cols031_3 : ∀ l : Fin 4, minorCols031 ((3 : Fin 5).succAbove l) = minorCols023 l := by
  decide +kernel
private theorem cutEdge031_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut031 A).submatrix Fin.succ (3 : Fin 5).succAbove = cut023 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows031 i) (cols031_3 l)
private theorem cols031_4 : ∀ l : Fin 4, minorCols031 ((4 : Fin 5).succAbove l) = minorCols015 l := by
  decide +kernel
private theorem cutEdge031_4 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut031 A).submatrix Fin.succ (4 : Fin 5).succAbove = cut015 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows031 i) (cols031_4 l)
theorem detJet031 (b c d e U : ℂ) :
    (cut031 (presentation b c d e U 0)).det = value (point b c d e U) D031 ∧
    HasDerivAt (fun T : ℂ => (cut031 (presentation b c d e U T)).det) (value (point b c d e U) J031) 0 := by
  have he : ∀ j : Fin 5, cut031 (presentation b c d e U 0) 0 j = entriesA031 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => cut031 (presentation b c d e U 0) 0 j = entriesA031 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 1 0
    · exact presentation_entry_zero b c d e U 1 1
    · exact presentation_entry_zero b c d e U 1 2
    · exact presentation_entry_zero b c d e U 1 3
    · exact presentation_entry_zero b c d e U 1 4
  have he' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => cut031 (presentation b c d e U T) 0 j) (entriesH031 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => cut031 (presentation b c d e U T) 0 j) (entriesH031 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 1 0
    · exact presentation_entry_hasDerivAt b c d e U 1 1
    · exact presentation_entry_hasDerivAt b c d e U 1 2
    · exact presentation_entry_hasDerivAt b c d e U 1 3
    · exact presentation_entry_hasDerivAt b c d e U 1 4
  have hd : ∀ j : Fin 5, ((cut031 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD031 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => ((cut031 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD031 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge031_0] using (detJet030 b c d e U).1
    · simpa only [cutEdge031_1] using (detJet029 b c d e U).1
    · simpa only [cutEdge031_2] using (detJet027 b c d e U).1
    · simpa only [cutEdge031_3] using (detJet023 b c d e U).1
    · simpa only [cutEdge031_4] using (detJet015 b c d e U).1
  have hd' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => ((cut031 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ031 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => ((cut031 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ031 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge031_0] using (detJet030 b c d e U).2
    · simpa only [cutEdge031_1] using (detJet029 b c d e U).2
    · simpa only [cutEdge031_2] using (detJet027 b c d e U).2
    · simpa only [cutEdge031_3] using (detJet023 b c d e U).2
    · simpa only [cutEdge031_4] using (detJet015 b c d e U).2
  have step := det_row_zero_jet (n := 4) (fun T : ℂ => cut031 (presentation b c d e U T))
    (entriesA031 (point b c d e U)) (entriesH031 (point b c d e U)) (childD031 (point b c d e U)) (childJ031 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity031 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity031 (point b c d e U)).symm⟩
end N6.ResultantMinors
