import N6.ResultantMinors.Determinants007_05
import N6.ResultantMinors.Arithmetic007
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.ResultantMinors
open N6.SparseCheck N6.Resultant6
private theorem rows063 : ∀ i : Fin 5, suffixRows6 i.succ = suffixRows5 i := by decide +kernel
private theorem cols063_0 : ∀ l : Fin 5, minorCols063 ((0 : Fin 6).succAbove l) = minorCols062 l := by
  decide +kernel
private theorem cutEdge063_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut063 A).submatrix Fin.succ (0 : Fin 6).succAbove = cut062 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows063 i) (cols063_0 l)
private theorem cols063_1 : ∀ l : Fin 5, minorCols063 ((1 : Fin 6).succAbove l) = minorCols061 l := by
  decide +kernel
private theorem cutEdge063_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut063 A).submatrix Fin.succ (1 : Fin 6).succAbove = cut061 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows063 i) (cols063_1 l)
private theorem cols063_2 : ∀ l : Fin 5, minorCols063 ((2 : Fin 6).succAbove l) = minorCols059 l := by
  decide +kernel
private theorem cutEdge063_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut063 A).submatrix Fin.succ (2 : Fin 6).succAbove = cut059 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows063 i) (cols063_2 l)
private theorem cols063_3 : ∀ l : Fin 5, minorCols063 ((3 : Fin 6).succAbove l) = minorCols055 l := by
  decide +kernel
private theorem cutEdge063_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut063 A).submatrix Fin.succ (3 : Fin 6).succAbove = cut055 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows063 i) (cols063_3 l)
private theorem cols063_4 : ∀ l : Fin 5, minorCols063 ((4 : Fin 6).succAbove l) = minorCols047 l := by
  decide +kernel
private theorem cutEdge063_4 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut063 A).submatrix Fin.succ (4 : Fin 6).succAbove = cut047 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows063 i) (cols063_4 l)
private theorem cols063_5 : ∀ l : Fin 5, minorCols063 ((5 : Fin 6).succAbove l) = minorCols031 l := by
  decide +kernel
private theorem cutEdge063_5 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut063 A).submatrix Fin.succ (5 : Fin 6).succAbove = cut031 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows063 i) (cols063_5 l)
theorem detJet063 (b c d e U : ℂ) :
    (cut063 (presentation b c d e U 0)).det = value (point b c d e U) D063 ∧
    HasDerivAt (fun T : ℂ => (cut063 (presentation b c d e U T)).det) (value (point b c d e U) J063) 0 := by
  have he : ∀ j : Fin 6, cut063 (presentation b c d e U 0) 0 j = entriesA063 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin6 (P := fun j => cut063 (presentation b c d e U 0) 0 j = entriesA063 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 0 0
    · exact presentation_entry_zero b c d e U 0 1
    · exact presentation_entry_zero b c d e U 0 2
    · exact presentation_entry_zero b c d e U 0 3
    · exact presentation_entry_zero b c d e U 0 4
    · exact presentation_entry_zero b c d e U 0 5
  have he' : ∀ j : Fin 6, HasDerivAt (fun T : ℂ => cut063 (presentation b c d e U T) 0 j) (entriesH063 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin6 (P := fun j => HasDerivAt (fun T : ℂ => cut063 (presentation b c d e U T) 0 j) (entriesH063 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 0 0
    · exact presentation_entry_hasDerivAt b c d e U 0 1
    · exact presentation_entry_hasDerivAt b c d e U 0 2
    · exact presentation_entry_hasDerivAt b c d e U 0 3
    · exact presentation_entry_hasDerivAt b c d e U 0 4
    · exact presentation_entry_hasDerivAt b c d e U 0 5
  have hd : ∀ j : Fin 6, ((cut063 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD063 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin6 (P := fun j => ((cut063 (presentation b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD063 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge063_0] using (detJet062 b c d e U).1
    · simpa only [cutEdge063_1] using (detJet061 b c d e U).1
    · simpa only [cutEdge063_2] using (detJet059 b c d e U).1
    · simpa only [cutEdge063_3] using (detJet055 b c d e U).1
    · simpa only [cutEdge063_4] using (detJet047 b c d e U).1
    · simpa only [cutEdge063_5] using (detJet031 b c d e U).1
  have hd' : ∀ j : Fin 6, HasDerivAt (fun T : ℂ => ((cut063 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ063 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin6 (P := fun j => HasDerivAt (fun T : ℂ => ((cut063 (presentation b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ063 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge063_0] using (detJet062 b c d e U).2
    · simpa only [cutEdge063_1] using (detJet061 b c d e U).2
    · simpa only [cutEdge063_2] using (detJet059 b c d e U).2
    · simpa only [cutEdge063_3] using (detJet055 b c d e U).2
    · simpa only [cutEdge063_4] using (detJet047 b c d e U).2
    · simpa only [cutEdge063_5] using (detJet031 b c d e U).2
  have step := det_row_zero_jet (n := 5) (fun T : ℂ => cut063 (presentation b c d e U T))
    (entriesA063 (point b c d e U)) (entriesH063 (point b c d e U)) (childD063 (point b c d e U)) (childJ063 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity063 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity063 (point b c d e U)).symm⟩
end N6.ResultantMinors
