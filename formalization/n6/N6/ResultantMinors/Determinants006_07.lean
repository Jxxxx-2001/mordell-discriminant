import N6.ResultantMinors.Determinants006_06
import N6.ResultantMinors.Arithmetic006
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
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
    (cut060 (presentation b c d e U 0)).det = value (point b c d e U) D060 ∧
    HasDerivAt (fun T : ℂ => (cut060 (presentation b c d e U T)).det) (value (point b c d e U) J060) 0 := by
  have he : ∀ j : Fin 4, cut060 (presentation b c d e U 0) 0 j = entriesA060 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut060 (presentation b c d e U 0) 0 j = entriesA060 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 4
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut060 (presentation b c d e U T) 0 j) (entriesH060 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut060 (presentation b c d e U T) 0 j) (entriesH060 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 4
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut060 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD060 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut060 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD060 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge060_0] using (detJet056 b c d e U).1
    · simpa only [cutEdge060_1] using (detJet052 b c d e U).1
    · simpa only [cutEdge060_2] using (detJet044 b c d e U).1
    · simpa only [cutEdge060_3] using (detJet028 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut060 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ060 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut060 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ060 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge060_0] using (detJet056 b c d e U).2
    · simpa only [cutEdge060_1] using (detJet052 b c d e U).2
    · simpa only [cutEdge060_2] using (detJet044 b c d e U).2
    · simpa only [cutEdge060_3] using (detJet028 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut060 (presentation b c d e U T))
    (entriesA060 (point b c d e U)) (entriesH060 (point b c d e U)) (childD060 (point b c d e U)) (childJ060 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity060 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity060 (point b c d e U)).symm⟩
end N6.ResultantMinors
