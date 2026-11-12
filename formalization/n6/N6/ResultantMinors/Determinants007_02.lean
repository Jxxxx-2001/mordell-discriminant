import N6.ResultantMinors.Determinants007_01
import N6.ResultantMinors.Arithmetic007
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem rows055 : ∀ i : Fin 4, suffixRows5 i.succ = suffixRows4 i := by decide +kernel
private theorem cols055_0 : ∀ l : Fin 4, minorCols055 ((0 : Fin 5).succAbove l) = minorCols054 l := by
  decide +kernel
private theorem cutEdge055_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut055 A).submatrix Fin.succ (0 : Fin 5).succAbove = cut054 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows055 i) (cols055_0 l)
private theorem cols055_1 : ∀ l : Fin 4, minorCols055 ((1 : Fin 5).succAbove l) = minorCols053 l := by
  decide +kernel
private theorem cutEdge055_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut055 A).submatrix Fin.succ (1 : Fin 5).succAbove = cut053 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows055 i) (cols055_1 l)
private theorem cols055_2 : ∀ l : Fin 4, minorCols055 ((2 : Fin 5).succAbove l) = minorCols051 l := by
  decide +kernel
private theorem cutEdge055_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut055 A).submatrix Fin.succ (2 : Fin 5).succAbove = cut051 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows055 i) (cols055_2 l)
private theorem cols055_3 : ∀ l : Fin 4, minorCols055 ((3 : Fin 5).succAbove l) = minorCols039 l := by
  decide +kernel
private theorem cutEdge055_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut055 A).submatrix Fin.succ (3 : Fin 5).succAbove = cut039 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows055 i) (cols055_3 l)
private theorem cols055_4 : ∀ l : Fin 4, minorCols055 ((4 : Fin 5).succAbove l) = minorCols023 l := by
  decide +kernel
private theorem cutEdge055_4 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut055 A).submatrix Fin.succ (4 : Fin 5).succAbove = cut023 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows055 i) (cols055_4 l)
theorem detJet055 (b c d e U : ℂ) :
    (cut055 (presentation b c d e U 0)).det = value (point b c d e U) D055 ∧
    HasDerivAt (fun T : ℂ => (cut055 (presentation b c d e U T)).det) (value (point b c d e U) J055) 0 := by
  have he : ∀ j : Fin 5, cut055 (presentation b c d e U 0) 0 j = entriesA055 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => cut055 (presentation b c d e U 0) 0 j = entriesA055 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 1 0
    · exact presentation_entry_zero b c d e U 1 1
    · exact presentation_entry_zero b c d e U 1 2
    · exact presentation_entry_zero b c d e U 1 4
    · exact presentation_entry_zero b c d e U 1 5
  have he' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => cut055 (presentation b c d e U T) 0 j) (entriesH055 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => cut055 (presentation b c d e U T) 0 j) (entriesH055 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 1 0
    · exact presentation_entry_hasDerivAt b c d e U 1 1
    · exact presentation_entry_hasDerivAt b c d e U 1 2
    · exact presentation_entry_hasDerivAt b c d e U 1 4
    · exact presentation_entry_hasDerivAt b c d e U 1 5
  have hd : ∀ j : Fin 5, ((cut055 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD055 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => ((cut055 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD055 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge055_0] using (detJet054 b c d e U).1
    · simpa only [cutEdge055_1] using (detJet053 b c d e U).1
    · simpa only [cutEdge055_2] using (detJet051 b c d e U).1
    · simpa only [cutEdge055_3] using (detJet039 b c d e U).1
    · simpa only [cutEdge055_4] using (detJet023 b c d e U).1
  have hd' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => ((cut055 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ055 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => ((cut055 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ055 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge055_0] using (detJet054 b c d e U).2
    · simpa only [cutEdge055_1] using (detJet053 b c d e U).2
    · simpa only [cutEdge055_2] using (detJet051 b c d e U).2
    · simpa only [cutEdge055_3] using (detJet039 b c d e U).2
    · simpa only [cutEdge055_4] using (detJet023 b c d e U).2
  have step := det_row_zero_jet (n := 4) (fun T : ℂ => cut055 (presentation b c d e U T))
    (entriesA055 (point b c d e U)) (entriesH055 (point b c d e U)) (childD055 (point b c d e U)) (childJ055 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity055 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity055 (point b c d e U)).symm⟩
end N6.ResultantMinors
