import N6.ResultantMinors.Determinants007_02
import N6.ResultantMinors.Arithmetic007
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem rows059 : ∀ i : Fin 4, suffixRows5 i.succ = suffixRows4 i := by decide +kernel
private theorem cols059_0 : ∀ l : Fin 4, minorCols059 ((0 : Fin 5).succAbove l) = minorCols058 l := by
  decide +kernel
private theorem cutEdge059_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut059 A).submatrix Fin.succ (0 : Fin 5).succAbove = cut058 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows059 i) (cols059_0 l)
private theorem cols059_1 : ∀ l : Fin 4, minorCols059 ((1 : Fin 5).succAbove l) = minorCols057 l := by
  decide +kernel
private theorem cutEdge059_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut059 A).submatrix Fin.succ (1 : Fin 5).succAbove = cut057 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows059 i) (cols059_1 l)
private theorem cols059_2 : ∀ l : Fin 4, minorCols059 ((2 : Fin 5).succAbove l) = minorCols051 l := by
  decide +kernel
private theorem cutEdge059_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut059 A).submatrix Fin.succ (2 : Fin 5).succAbove = cut051 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows059 i) (cols059_2 l)
private theorem cols059_3 : ∀ l : Fin 4, minorCols059 ((3 : Fin 5).succAbove l) = minorCols043 l := by
  decide +kernel
private theorem cutEdge059_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut059 A).submatrix Fin.succ (3 : Fin 5).succAbove = cut043 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows059 i) (cols059_3 l)
private theorem cols059_4 : ∀ l : Fin 4, minorCols059 ((4 : Fin 5).succAbove l) = minorCols027 l := by
  decide +kernel
private theorem cutEdge059_4 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut059 A).submatrix Fin.succ (4 : Fin 5).succAbove = cut027 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows059 i) (cols059_4 l)
theorem detJet059 (b c d e U : ℂ) :
    (cut059 (presentation b c d e U 0)).det = value (point b c d e U) D059 ∧
    HasDerivAt (fun T : ℂ => (cut059 (presentation b c d e U T)).det) (value (point b c d e U) J059) 0 := by
  have he : ∀ j : Fin 5, cut059 (presentation b c d e U 0) 0 j = entriesA059 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => cut059 (presentation b c d e U 0) 0 j = entriesA059 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 1 0
    · exact presentation_entry_zero b c d e U 1 1
    · exact presentation_entry_zero b c d e U 1 3
    · exact presentation_entry_zero b c d e U 1 4
    · exact presentation_entry_zero b c d e U 1 5
  have he' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => cut059 (presentation b c d e U T) 0 j) (entriesH059 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => cut059 (presentation b c d e U T) 0 j) (entriesH059 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 1 0
    · exact presentation_entry_hasDerivAt b c d e U 1 1
    · exact presentation_entry_hasDerivAt b c d e U 1 3
    · exact presentation_entry_hasDerivAt b c d e U 1 4
    · exact presentation_entry_hasDerivAt b c d e U 1 5
  have hd : ∀ j : Fin 5, ((cut059 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD059 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => ((cut059 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD059 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge059_0] using (detJet058 b c d e U).1
    · simpa only [cutEdge059_1] using (detJet057 b c d e U).1
    · simpa only [cutEdge059_2] using (detJet051 b c d e U).1
    · simpa only [cutEdge059_3] using (detJet043 b c d e U).1
    · simpa only [cutEdge059_4] using (detJet027 b c d e U).1
  have hd' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => ((cut059 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ059 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => ((cut059 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ059 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge059_0] using (detJet058 b c d e U).2
    · simpa only [cutEdge059_1] using (detJet057 b c d e U).2
    · simpa only [cutEdge059_2] using (detJet051 b c d e U).2
    · simpa only [cutEdge059_3] using (detJet043 b c d e U).2
    · simpa only [cutEdge059_4] using (detJet027 b c d e U).2
  have step := det_row_zero_jet (n := 4) (fun T : ℂ => cut059 (presentation b c d e U T))
    (entriesA059 (point b c d e U)) (entriesH059 (point b c d e U)) (childD059 (point b c d e U)) (childJ059 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity059 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity059 (point b c d e U)).symm⟩
end N6.ResultantMinors
