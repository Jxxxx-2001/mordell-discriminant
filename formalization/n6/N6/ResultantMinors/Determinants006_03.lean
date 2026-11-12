import N6.ResultantMinors.Determinants006_02
import N6.ResultantMinors.Arithmetic006
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
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
    (cut053 (presentation b c d e U 0)).det = value (point b c d e U) D053 ∧
    HasDerivAt (fun T : ℂ => (cut053 (presentation b c d e U T)).det) (value (point b c d e U) J053) 0 := by
  have he : ∀ j : Fin 4, cut053 (presentation b c d e U 0) 0 j = entriesA053 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => cut053 (presentation b c d e U 0) 0 j = entriesA053 (point b c d e U) j) ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 2 0
    · exact presentation_entry_zero b c d e U 2 2
    · exact presentation_entry_zero b c d e U 2 4
    · exact presentation_entry_zero b c d e U 2 5
  have he' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => cut053 (presentation b c d e U T) 0 j) (entriesH053 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => cut053 (presentation b c d e U T) 0 j) (entriesH053 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 2 0
    · exact presentation_entry_hasDerivAt b c d e U 2 2
    · exact presentation_entry_hasDerivAt b c d e U 2 4
    · exact presentation_entry_hasDerivAt b c d e U 2 5
  have hd : ∀ j : Fin 4, ((cut053 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD053 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => ((cut053 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD053 (point b c d e U) j) ?_ ?_ ?_ ?_
    · simpa only [cutEdge053_0] using (detJet052 b c d e U).1
    · simpa only [cutEdge053_1] using (detJet049 b c d e U).1
    · simpa only [cutEdge053_2] using (detJet037 b c d e U).1
    · simpa only [cutEdge053_3] using (detJet021 b c d e U).1
  have hd' : ∀ j : Fin 4, HasDerivAt (fun T : ℂ => ((cut053 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ053 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin4 (P := fun j => HasDerivAt (fun T : ℂ => ((cut053 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ053 (point b c d e U) j) 0) ?_ ?_ ?_ ?_
    · simpa only [cutEdge053_0] using (detJet052 b c d e U).2
    · simpa only [cutEdge053_1] using (detJet049 b c d e U).2
    · simpa only [cutEdge053_2] using (detJet037 b c d e U).2
    · simpa only [cutEdge053_3] using (detJet021 b c d e U).2
  have step := det_row_zero_jet (n := 3) (fun T : ℂ => cut053 (presentation b c d e U T))
    (entriesA053 (point b c d e U)) (entriesH053 (point b c d e U)) (childD053 (point b c d e U)) (childJ053 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity053 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity053 (point b c d e U)).symm⟩
end N6.ResultantMinors
