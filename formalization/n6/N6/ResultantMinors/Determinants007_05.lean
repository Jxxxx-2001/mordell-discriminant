import N6.ResultantMinors.Determinants007_04
import N6.ResultantMinors.Arithmetic007
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem rows062 : ∀ i : Fin 4, suffixRows5 i.succ = suffixRows4 i := by decide +kernel
private theorem cols062_0 : ∀ l : Fin 4, minorCols062 ((0 : Fin 5).succAbove l) = minorCols060 l := by
  decide +kernel
private theorem cutEdge062_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut062 A).submatrix Fin.succ (0 : Fin 5).succAbove = cut060 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows062 i) (cols062_0 l)
private theorem cols062_1 : ∀ l : Fin 4, minorCols062 ((1 : Fin 5).succAbove l) = minorCols058 l := by
  decide +kernel
private theorem cutEdge062_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut062 A).submatrix Fin.succ (1 : Fin 5).succAbove = cut058 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows062 i) (cols062_1 l)
private theorem cols062_2 : ∀ l : Fin 4, minorCols062 ((2 : Fin 5).succAbove l) = minorCols054 l := by
  decide +kernel
private theorem cutEdge062_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut062 A).submatrix Fin.succ (2 : Fin 5).succAbove = cut054 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows062 i) (cols062_2 l)
private theorem cols062_3 : ∀ l : Fin 4, minorCols062 ((3 : Fin 5).succAbove l) = minorCols046 l := by
  decide +kernel
private theorem cutEdge062_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut062 A).submatrix Fin.succ (3 : Fin 5).succAbove = cut046 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows062 i) (cols062_3 l)
private theorem cols062_4 : ∀ l : Fin 4, minorCols062 ((4 : Fin 5).succAbove l) = minorCols030 l := by
  decide +kernel
private theorem cutEdge062_4 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut062 A).submatrix Fin.succ (4 : Fin 5).succAbove = cut030 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows062 i) (cols062_4 l)
theorem detJet062 (b c d e U : ℂ) :
    (cut062 (presentation b c d e U 0)).det = value (point b c d e U) D062 ∧
    HasDerivAt (fun T : ℂ => (cut062 (presentation b c d e U T)).det) (value (point b c d e U) J062) 0 := by
  have he : ∀ j : Fin 5, cut062 (presentation b c d e U 0) 0 j = entriesA062 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => cut062 (presentation b c d e U 0) 0 j = entriesA062 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 1 1
    · exact presentation_entry_zero b c d e U 1 2
    · exact presentation_entry_zero b c d e U 1 3
    · exact presentation_entry_zero b c d e U 1 4
    · exact presentation_entry_zero b c d e U 1 5
  have he' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => cut062 (presentation b c d e U T) 0 j) (entriesH062 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => cut062 (presentation b c d e U T) 0 j) (entriesH062 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 1 1
    · exact presentation_entry_hasDerivAt b c d e U 1 2
    · exact presentation_entry_hasDerivAt b c d e U 1 3
    · exact presentation_entry_hasDerivAt b c d e U 1 4
    · exact presentation_entry_hasDerivAt b c d e U 1 5
  have hd : ∀ j : Fin 5, ((cut062 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD062 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => ((cut062 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD062 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge062_0] using (detJet060 b c d e U).1
    · simpa only [cutEdge062_1] using (detJet058 b c d e U).1
    · simpa only [cutEdge062_2] using (detJet054 b c d e U).1
    · simpa only [cutEdge062_3] using (detJet046 b c d e U).1
    · simpa only [cutEdge062_4] using (detJet030 b c d e U).1
  have hd' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => ((cut062 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ062 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => ((cut062 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ062 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge062_0] using (detJet060 b c d e U).2
    · simpa only [cutEdge062_1] using (detJet058 b c d e U).2
    · simpa only [cutEdge062_2] using (detJet054 b c d e U).2
    · simpa only [cutEdge062_3] using (detJet046 b c d e U).2
    · simpa only [cutEdge062_4] using (detJet030 b c d e U).2
  have step := det_row_zero_jet (n := 4) (fun T : ℂ => cut062 (presentation b c d e U T))
    (entriesA062 (point b c d e U)) (entriesH062 (point b c d e U)) (childD062 (point b c d e U)) (childJ062 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity062 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity062 (point b c d e U)).symm⟩
end N6.ResultantMinors
