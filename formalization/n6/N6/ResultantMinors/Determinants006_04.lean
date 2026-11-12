import N6.ResultantMinors.Determinants006_03
import N6.ResultantMinors.Arithmetic006
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
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
    (cut054 (presentation b c d e U 0)).det = value (point b c d e U) D054 ∧
    HasDerivAt (fun T : ℂ => (cut054 (presentation b c d e U T)).det) (value (point b c d e U) J054) 0 := by
  have he : ∀ j : Fin 4, cut054 (presentation b c d e U 0) 0 j = entriesA054 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut054 (presentation b c d e U 0) 0 j = entriesA054 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 1
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 4
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut054 (presentation b c d e U T) 0 j) (entriesH054 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut054 (presentation b c d e U T) 0 j) (entriesH054 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 1
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 4
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut054 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD054 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut054 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD054 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge054_0] using (detJet052 b c d e U).1
    · simpa only [cutEdge054_1] using (detJet050 b c d e U).1
    · simpa only [cutEdge054_2] using (detJet038 b c d e U).1
    · simpa only [cutEdge054_3] using (detJet022 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut054 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ054 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut054 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ054 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge054_0] using (detJet052 b c d e U).2
    · simpa only [cutEdge054_1] using (detJet050 b c d e U).2
    · simpa only [cutEdge054_2] using (detJet038 b c d e U).2
    · simpa only [cutEdge054_3] using (detJet022 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut054 (presentation b c d e U T))
    (entriesA054 (point b c d e U)) (entriesH054 (point b c d e U)) (childD054 (point b c d e U)) (childJ054 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity054 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity054 (point b c d e U)).symm⟩
end N6.ResultantMinors
