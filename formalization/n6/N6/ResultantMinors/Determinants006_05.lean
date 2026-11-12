import N6.ResultantMinors.Determinants006_04
import N6.ResultantMinors.Arithmetic006
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
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
    (cut057 (presentation b c d e U 0)).det = value (point b c d e U) D057 ∧
    HasDerivAt (fun T : ℂ => (cut057 (presentation b c d e U T)).det) (value (point b c d e U) J057) 0 := by
  have he : ∀ j : Fin 4, cut057 (presentation b c d e U 0) 0 j = entriesA057 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut057 (presentation b c d e U 0) 0 j = entriesA057 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 4
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut057 (presentation b c d e U T) 0 j) (entriesH057 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut057 (presentation b c d e U T) 0 j) (entriesH057 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 4
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut057 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD057 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut057 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD057 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge057_0] using (detJet056 b c d e U).1
    · simpa only [cutEdge057_1] using (detJet049 b c d e U).1
    · simpa only [cutEdge057_2] using (detJet041 b c d e U).1
    · simpa only [cutEdge057_3] using (detJet025 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut057 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ057 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut057 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ057 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge057_0] using (detJet056 b c d e U).2
    · simpa only [cutEdge057_1] using (detJet049 b c d e U).2
    · simpa only [cutEdge057_2] using (detJet041 b c d e U).2
    · simpa only [cutEdge057_3] using (detJet025 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut057 (presentation b c d e U T))
    (entriesA057 (point b c d e U)) (entriesH057 (point b c d e U)) (childD057 (point b c d e U)) (childJ057 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity057 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity057 (point b c d e U)).symm⟩
end N6.ResultantMinors
