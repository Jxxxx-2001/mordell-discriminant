import N6.ResultantMinors.Determinants007_03
import N6.ResultantMinors.Arithmetic007
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem rows061 : ∀ i : Fin 4, suffixRows5 i.succ = suffixRows4 i := by decide +kernel
private theorem cols061_0 : ∀ l : Fin 4, minorCols061 ((0 : Fin 5).succAbove l) = minorCols060 l := by
  decide +kernel
private theorem cutEdge061_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut061 A).submatrix Fin.succ (0 : Fin 5).succAbove = cut060 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows061 i) (cols061_0 l)
private theorem cols061_1 : ∀ l : Fin 4, minorCols061 ((1 : Fin 5).succAbove l) = minorCols057 l := by
  decide +kernel
private theorem cutEdge061_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut061 A).submatrix Fin.succ (1 : Fin 5).succAbove = cut057 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows061 i) (cols061_1 l)
private theorem cols061_2 : ∀ l : Fin 4, minorCols061 ((2 : Fin 5).succAbove l) = minorCols053 l := by
  decide +kernel
private theorem cutEdge061_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut061 A).submatrix Fin.succ (2 : Fin 5).succAbove = cut053 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows061 i) (cols061_2 l)
private theorem cols061_3 : ∀ l : Fin 4, minorCols061 ((3 : Fin 5).succAbove l) = minorCols045 l := by
  decide +kernel
private theorem cutEdge061_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut061 A).submatrix Fin.succ (3 : Fin 5).succAbove = cut045 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows061 i) (cols061_3 l)
private theorem cols061_4 : ∀ l : Fin 4, minorCols061 ((4 : Fin 5).succAbove l) = minorCols029 l := by
  decide +kernel
private theorem cutEdge061_4 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut061 A).submatrix Fin.succ (4 : Fin 5).succAbove = cut029 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows061 i) (cols061_4 l)
theorem detJet061 (b c d e U : ℂ) :
    (cut061 (presentation b c d e U 0)).det = value (point b c d e U) D061 ∧
    HasDerivAt (fun T : ℂ => (cut061 (presentation b c d e U T)).det) (value (point b c d e U) J061) 0 := by
  have he : ∀ j : Fin 5, cut061 (presentation b c d e U 0) 0 j = entriesA061 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => cut061 (presentation b c d e U 0) 0 j = entriesA061 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 1 0
    · exact presentation_entry_zero b c d e U 1 2
    · exact presentation_entry_zero b c d e U 1 3
    · exact presentation_entry_zero b c d e U 1 4
    · exact presentation_entry_zero b c d e U 1 5
  have he' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => cut061 (presentation b c d e U T) 0 j) (entriesH061 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => cut061 (presentation b c d e U T) 0 j) (entriesH061 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 1 0
    · exact presentation_entry_hasDerivAt b c d e U 1 2
    · exact presentation_entry_hasDerivAt b c d e U 1 3
    · exact presentation_entry_hasDerivAt b c d e U 1 4
    · exact presentation_entry_hasDerivAt b c d e U 1 5
  have hd : ∀ j : Fin 5, ((cut061 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD061 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => ((cut061 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD061 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge061_0] using (detJet060 b c d e U).1
    · simpa only [cutEdge061_1] using (detJet057 b c d e U).1
    · simpa only [cutEdge061_2] using (detJet053 b c d e U).1
    · simpa only [cutEdge061_3] using (detJet045 b c d e U).1
    · simpa only [cutEdge061_4] using (detJet029 b c d e U).1
  have hd' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => ((cut061 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ061 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => ((cut061 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ061 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge061_0] using (detJet060 b c d e U).2
    · simpa only [cutEdge061_1] using (detJet057 b c d e U).2
    · simpa only [cutEdge061_2] using (detJet053 b c d e U).2
    · simpa only [cutEdge061_3] using (detJet045 b c d e U).2
    · simpa only [cutEdge061_4] using (detJet029 b c d e U).2
  have step := det_row_zero_jet (n := 4) (fun T : ℂ => cut061 (presentation b c d e U T))
    (entriesA061 (point b c d e U)) (entriesH061 (point b c d e U)) (childD061 (point b c d e U)) (childJ061 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity061 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity061 (point b c d e U)).symm⟩
end N6.ResultantMinors
