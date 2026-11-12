import N6.ResultantMinors.Determinants006_05
import N6.ResultantMinors.Arithmetic006
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
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
    (cut058 (presentation b c d e U 0)).det = value (point b c d e U) D058 ∧
    HasDerivAt (fun T : ℂ => (cut058 (presentation b c d e U T)).det) (value (point b c d e U) J058) 0 := by
  have he : ∀ j : Fin 4, cut058 (presentation b c d e U 0) 0 j = entriesA058 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut058 (presentation b c d e U 0) 0 j = entriesA058 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 3
    · exact presentation_entry_zero b c d e U 2 4
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut058 (presentation b c d e U T) 0 j) (entriesH058 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut058 (presentation b c d e U T) 0 j) (entriesH058 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 3
    · exact presentation_entry_hasDerivAt b c d e U 2 4
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut058 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD058 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut058 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD058 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge058_0] using (detJet056 b c d e U).1
    · simpa only [cutEdge058_1] using (detJet050 b c d e U).1
    · simpa only [cutEdge058_2] using (detJet042 b c d e U).1
    · simpa only [cutEdge058_3] using (detJet026 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut058 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ058 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut058 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ058 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge058_0] using (detJet056 b c d e U).2
    · simpa only [cutEdge058_1] using (detJet050 b c d e U).2
    · simpa only [cutEdge058_2] using (detJet042 b c d e U).2
    · simpa only [cutEdge058_3] using (detJet026 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut058 (presentation b c d e U T))
    (entriesA058 (point b c d e U)) (entriesH058 (point b c d e U)) (childD058 (point b c d e U)) (childJ058 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity058 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity058 (point b c d e U)).symm⟩
end N6.ResultantMinors
