import N6.ResultantMinors.Determinants006_01
import N6.ResultantMinors.Arithmetic006
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
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
    (cut051 (presentation b c d e U 0)).det = value (point b c d e U) D051 ∧
    HasDerivAt (fun T : ℂ => (cut051 (presentation b c d e U T)).det) (value (point b c d e U) J051) 0 := by
  have he : ∀ j : Fin 4, cut051 (presentation b c d e U 0) 0 j = entriesA051 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut051 (presentation b c d e U 0) 0 j = entriesA051 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 4
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut051 (presentation b c d e U T) 0 j) (entriesH051 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut051 (presentation b c d e U T) 0 j) (entriesH051 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 4
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut051 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD051 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut051 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD051 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge051_0] using (detJet050 b c d e U).1
    · simpa only [cutEdge051_1] using (detJet049 b c d e U).1
    · simpa only [cutEdge051_2] using (detJet035 b c d e U).1
    · simpa only [cutEdge051_3] using (detJet019 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut051 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ051 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut051 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ051 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge051_0] using (detJet050 b c d e U).2
    · simpa only [cutEdge051_1] using (detJet049 b c d e U).2
    · simpa only [cutEdge051_2] using (detJet035 b c d e U).2
    · simpa only [cutEdge051_3] using (detJet019 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut051 (presentation b c d e U T))
    (entriesA051 (point b c d e U)) (entriesH051 (point b c d e U)) (childD051 (point b c d e U)) (childJ051 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity051 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity051 (point b c d e U)).symm⟩
end N6.ResultantMinors
