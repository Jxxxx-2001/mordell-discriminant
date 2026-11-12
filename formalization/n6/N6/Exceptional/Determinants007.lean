import N6.Exceptional.Determinants006
import N6.Exceptional.Arithmetic007
import N6.ResultantMinors.JetFiniteElim
set_option autoImplicit false
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
namespace N6.Exceptional
open N6.SparseCheck N6.Resultant6
private theorem rows031 : ∀ i : Fin 4, suffixRows5 i.succ = suffixRows4 i := by decide +kernel
private theorem cols031_0 : ∀ l : Fin 4, minorCols031 ((0 : Fin 5).succAbove l) = minorCols030 l := by
  decide +kernel
private theorem cutEdge031_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut031 A).submatrix Fin.succ (0 : Fin 5).succAbove = cut030 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows031 i) (cols031_0 l)
private theorem cols031_1 : ∀ l : Fin 4, minorCols031 ((1 : Fin 5).succAbove l) = minorCols029 l := by
  decide +kernel
private theorem cutEdge031_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut031 A).submatrix Fin.succ (1 : Fin 5).succAbove = cut029 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows031 i) (cols031_1 l)
private theorem cols031_2 : ∀ l : Fin 4, minorCols031 ((2 : Fin 5).succAbove l) = minorCols027 l := by
  decide +kernel
private theorem cutEdge031_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut031 A).submatrix Fin.succ (2 : Fin 5).succAbove = cut027 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows031 i) (cols031_2 l)
private theorem cols031_3 : ∀ l : Fin 4, minorCols031 ((3 : Fin 5).succAbove l) = minorCols023 l := by
  decide +kernel
private theorem cutEdge031_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut031 A).submatrix Fin.succ (3 : Fin 5).succAbove = cut023 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows031 i) (cols031_3 l)
private theorem cols031_4 : ∀ l : Fin 4, minorCols031 ((4 : Fin 5).succAbove l) = minorCols015 l := by
  decide +kernel
private theorem cutEdge031_4 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut031 A).submatrix Fin.succ (4 : Fin 5).succAbove = cut015 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows031 i) (cols031_4 l)
theorem detJet031 (b c d e U : ℂ) :
    (cut031 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D031 ∧
    HasDerivAt (fun T : ℂ => (cut031 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J031) 0 := by
  have he : ∀ j : Fin 5, cut031 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA031 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => cut031 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA031 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 1 0
    · exact presentation_entry_zero b c d e U 1 1
    · exact presentation_entry_zero b c d e U 1 2
    · exact presentation_entry_zero b c d e U 1 3
    · exact presentation_entry_zero b c d e U 1 4
  have he' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => cut031 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH031 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => cut031 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH031 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 1 0
    · exact presentation_entry_hasDerivAt b c d e U 1 1
    · exact presentation_entry_hasDerivAt b c d e U 1 2
    · exact presentation_entry_hasDerivAt b c d e U 1 3
    · exact presentation_entry_hasDerivAt b c d e U 1 4
  have hd : ∀ j : Fin 5, ((cut031 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD031 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => ((cut031 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD031 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge031_0] using (detJet030 b c d e U).1
    · simpa only [cutEdge031_1] using (detJet029 b c d e U).1
    · simpa only [cutEdge031_2] using (detJet027 b c d e U).1
    · simpa only [cutEdge031_3] using (detJet023 b c d e U).1
    · simpa only [cutEdge031_4] using (detJet015 b c d e U).1
  have hd' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => ((cut031 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ031 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => ((cut031 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ031 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge031_0] using (detJet030 b c d e U).2
    · simpa only [cutEdge031_1] using (detJet029 b c d e U).2
    · simpa only [cutEdge031_2] using (detJet027 b c d e U).2
    · simpa only [cutEdge031_3] using (detJet023 b c d e U).2
    · simpa only [cutEdge031_4] using (detJet015 b c d e U).2
  have step := det_row_zero_jet (n := 4) (fun T : ℂ => cut031 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA031 (point b c d e U)) (entriesH031 (point b c d e U)) (childD031 (point b c d e U)) (childJ031 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity031 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity031 (point b c d e U)).symm⟩
private theorem rows047 : ∀ i : Fin 4, suffixRows5 i.succ = suffixRows4 i := by decide +kernel
private theorem cols047_0 : ∀ l : Fin 4, minorCols047 ((0 : Fin 5).succAbove l) = minorCols046 l := by
  decide +kernel
private theorem cutEdge047_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut047 A).submatrix Fin.succ (0 : Fin 5).succAbove = cut046 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows047 i) (cols047_0 l)
private theorem cols047_1 : ∀ l : Fin 4, minorCols047 ((1 : Fin 5).succAbove l) = minorCols045 l := by
  decide +kernel
private theorem cutEdge047_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut047 A).submatrix Fin.succ (1 : Fin 5).succAbove = cut045 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows047 i) (cols047_1 l)
private theorem cols047_2 : ∀ l : Fin 4, minorCols047 ((2 : Fin 5).succAbove l) = minorCols043 l := by
  decide +kernel
private theorem cutEdge047_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut047 A).submatrix Fin.succ (2 : Fin 5).succAbove = cut043 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows047 i) (cols047_2 l)
private theorem cols047_3 : ∀ l : Fin 4, minorCols047 ((3 : Fin 5).succAbove l) = minorCols039 l := by
  decide +kernel
private theorem cutEdge047_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut047 A).submatrix Fin.succ (3 : Fin 5).succAbove = cut039 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows047 i) (cols047_3 l)
private theorem cols047_4 : ∀ l : Fin 4, minorCols047 ((4 : Fin 5).succAbove l) = minorCols015 l := by
  decide +kernel
private theorem cutEdge047_4 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut047 A).submatrix Fin.succ (4 : Fin 5).succAbove = cut015 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows047 i) (cols047_4 l)
theorem detJet047 (b c d e U : ℂ) :
    (cut047 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D047 ∧
    HasDerivAt (fun T : ℂ => (cut047 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J047) 0 := by
  have he : ∀ j : Fin 5, cut047 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA047 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => cut047 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA047 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 1 0
    · exact presentation_entry_zero b c d e U 1 1
    · exact presentation_entry_zero b c d e U 1 2
    · exact presentation_entry_zero b c d e U 1 3
    · exact presentation_entry_zero b c d e U 1 5
  have he' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => cut047 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH047 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => cut047 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH047 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 1 0
    · exact presentation_entry_hasDerivAt b c d e U 1 1
    · exact presentation_entry_hasDerivAt b c d e U 1 2
    · exact presentation_entry_hasDerivAt b c d e U 1 3
    · exact presentation_entry_hasDerivAt b c d e U 1 5
  have hd : ∀ j : Fin 5, ((cut047 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD047 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => ((cut047 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD047 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge047_0] using (detJet046 b c d e U).1
    · simpa only [cutEdge047_1] using (detJet045 b c d e U).1
    · simpa only [cutEdge047_2] using (detJet043 b c d e U).1
    · simpa only [cutEdge047_3] using (detJet039 b c d e U).1
    · simpa only [cutEdge047_4] using (detJet015 b c d e U).1
  have hd' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => ((cut047 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ047 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => ((cut047 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ047 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge047_0] using (detJet046 b c d e U).2
    · simpa only [cutEdge047_1] using (detJet045 b c d e U).2
    · simpa only [cutEdge047_2] using (detJet043 b c d e U).2
    · simpa only [cutEdge047_3] using (detJet039 b c d e U).2
    · simpa only [cutEdge047_4] using (detJet015 b c d e U).2
  have step := det_row_zero_jet (n := 4) (fun T : ℂ => cut047 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA047 (point b c d e U)) (entriesH047 (point b c d e U)) (childD047 (point b c d e U)) (childJ047 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity047 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity047 (point b c d e U)).symm⟩
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
    (cut055 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D055 ∧
    HasDerivAt (fun T : ℂ => (cut055 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J055) 0 := by
  have he : ∀ j : Fin 5, cut055 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA055 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => cut055 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA055 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 1 0
    · exact presentation_entry_zero b c d e U 1 1
    · exact presentation_entry_zero b c d e U 1 2
    · exact presentation_entry_zero b c d e U 1 4
    · exact presentation_entry_zero b c d e U 1 5
  have he' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => cut055 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH055 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => cut055 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH055 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 1 0
    · exact presentation_entry_hasDerivAt b c d e U 1 1
    · exact presentation_entry_hasDerivAt b c d e U 1 2
    · exact presentation_entry_hasDerivAt b c d e U 1 4
    · exact presentation_entry_hasDerivAt b c d e U 1 5
  have hd : ∀ j : Fin 5, ((cut055 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD055 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => ((cut055 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD055 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge055_0] using (detJet054 b c d e U).1
    · simpa only [cutEdge055_1] using (detJet053 b c d e U).1
    · simpa only [cutEdge055_2] using (detJet051 b c d e U).1
    · simpa only [cutEdge055_3] using (detJet039 b c d e U).1
    · simpa only [cutEdge055_4] using (detJet023 b c d e U).1
  have hd' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => ((cut055 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ055 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => ((cut055 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ055 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge055_0] using (detJet054 b c d e U).2
    · simpa only [cutEdge055_1] using (detJet053 b c d e U).2
    · simpa only [cutEdge055_2] using (detJet051 b c d e U).2
    · simpa only [cutEdge055_3] using (detJet039 b c d e U).2
    · simpa only [cutEdge055_4] using (detJet023 b c d e U).2
  have step := det_row_zero_jet (n := 4) (fun T : ℂ => cut055 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA055 (point b c d e U)) (entriesH055 (point b c d e U)) (childD055 (point b c d e U)) (childJ055 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity055 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity055 (point b c d e U)).symm⟩
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
    (cut059 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D059 ∧
    HasDerivAt (fun T : ℂ => (cut059 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J059) 0 := by
  have he : ∀ j : Fin 5, cut059 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA059 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => cut059 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA059 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 1 0
    · exact presentation_entry_zero b c d e U 1 1
    · exact presentation_entry_zero b c d e U 1 3
    · exact presentation_entry_zero b c d e U 1 4
    · exact presentation_entry_zero b c d e U 1 5
  have he' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => cut059 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH059 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => cut059 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH059 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 1 0
    · exact presentation_entry_hasDerivAt b c d e U 1 1
    · exact presentation_entry_hasDerivAt b c d e U 1 3
    · exact presentation_entry_hasDerivAt b c d e U 1 4
    · exact presentation_entry_hasDerivAt b c d e U 1 5
  have hd : ∀ j : Fin 5, ((cut059 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD059 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => ((cut059 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD059 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge059_0] using (detJet058 b c d e U).1
    · simpa only [cutEdge059_1] using (detJet057 b c d e U).1
    · simpa only [cutEdge059_2] using (detJet051 b c d e U).1
    · simpa only [cutEdge059_3] using (detJet043 b c d e U).1
    · simpa only [cutEdge059_4] using (detJet027 b c d e U).1
  have hd' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => ((cut059 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ059 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => ((cut059 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ059 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge059_0] using (detJet058 b c d e U).2
    · simpa only [cutEdge059_1] using (detJet057 b c d e U).2
    · simpa only [cutEdge059_2] using (detJet051 b c d e U).2
    · simpa only [cutEdge059_3] using (detJet043 b c d e U).2
    · simpa only [cutEdge059_4] using (detJet027 b c d e U).2
  have step := det_row_zero_jet (n := 4) (fun T : ℂ => cut059 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA059 (point b c d e U)) (entriesH059 (point b c d e U)) (childD059 (point b c d e U)) (childJ059 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity059 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity059 (point b c d e U)).symm⟩
private theorem rows061 : ∀ i : Fin 4, suffixRows5 i.succ = suffixRows4 i := by decide +kernel
private theorem cols061_0 : ∀ l : Fin 4, minorCols061 ((0 : Fin 5).succAbove l) = minorCols060 l := by
  decide +kernel
private theorem cutEdge061_0 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut061 A).submatrix Fin.succ (0 : Fin 5).succAbove = cut060 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows061 i) (cols061_0 l)
private theorem cols061_1 : ∀ l : Fin 4, minorCols061 ((1 : Fin 5).succAbove l) = minorCols057 l := by
  decide +kernel
private theorem cutEdge061_1 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut061 A).submatrix Fin.succ (1 : Fin 5).succAbove = cut057 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows061 i) (cols061_1 l)
private theorem cols061_2 : ∀ l : Fin 4, minorCols061 ((2 : Fin 5).succAbove l) = minorCols053 l := by
  decide +kernel
private theorem cutEdge061_2 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut061 A).submatrix Fin.succ (2 : Fin 5).succAbove = cut053 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows061 i) (cols061_2 l)
private theorem cols061_3 : ∀ l : Fin 4, minorCols061 ((3 : Fin 5).succAbove l) = minorCols045 l := by
  decide +kernel
private theorem cutEdge061_3 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut061 A).submatrix Fin.succ (3 : Fin 5).succAbove = cut045 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows061 i) (cols061_3 l)
private theorem cols061_4 : ∀ l : Fin 4, minorCols061 ((4 : Fin 5).succAbove l) = minorCols029 l := by
  decide +kernel
private theorem cutEdge061_4 {R : Type*} (A : Matrix (Fin 6) (Fin 6) R) :
    (cut061 A).submatrix Fin.succ (4 : Fin 5).succAbove = cut029 A := by
  apply Matrix.ext
  intro i l
  exact congrArg₂ A (rows061 i) (cols061_4 l)
theorem detJet061 (b c d e U : ℂ) :
    (cut061 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D061 ∧
    HasDerivAt (fun T : ℂ => (cut061 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J061) 0 := by
  have he : ∀ j : Fin 5, cut061 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA061 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => cut061 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA061 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 1 0
    · exact presentation_entry_zero b c d e U 1 2
    · exact presentation_entry_zero b c d e U 1 3
    · exact presentation_entry_zero b c d e U 1 4
    · exact presentation_entry_zero b c d e U 1 5
  have he' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => cut061 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH061 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => cut061 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH061 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 1 0
    · exact presentation_entry_hasDerivAt b c d e U 1 2
    · exact presentation_entry_hasDerivAt b c d e U 1 3
    · exact presentation_entry_hasDerivAt b c d e U 1 4
    · exact presentation_entry_hasDerivAt b c d e U 1 5
  have hd : ∀ j : Fin 5, ((cut061 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD061 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => ((cut061 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD061 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge061_0] using (detJet060 b c d e U).1
    · simpa only [cutEdge061_1] using (detJet057 b c d e U).1
    · simpa only [cutEdge061_2] using (detJet053 b c d e U).1
    · simpa only [cutEdge061_3] using (detJet045 b c d e U).1
    · simpa only [cutEdge061_4] using (detJet029 b c d e U).1
  have hd' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => ((cut061 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ061 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => ((cut061 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ061 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge061_0] using (detJet060 b c d e U).2
    · simpa only [cutEdge061_1] using (detJet057 b c d e U).2
    · simpa only [cutEdge061_2] using (detJet053 b c d e U).2
    · simpa only [cutEdge061_3] using (detJet045 b c d e U).2
    · simpa only [cutEdge061_4] using (detJet029 b c d e U).2
  have step := det_row_zero_jet (n := 4) (fun T : ℂ => cut061 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA061 (point b c d e U)) (entriesH061 (point b c d e U)) (childD061 (point b c d e U)) (childJ061 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity061 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity061 (point b c d e U)).symm⟩
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
    (cut062 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D062 ∧
    HasDerivAt (fun T : ℂ => (cut062 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J062) 0 := by
  have he : ∀ j : Fin 5, cut062 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA062 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => cut062 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA062 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 1 1
    · exact presentation_entry_zero b c d e U 1 2
    · exact presentation_entry_zero b c d e U 1 3
    · exact presentation_entry_zero b c d e U 1 4
    · exact presentation_entry_zero b c d e U 1 5
  have he' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => cut062 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH062 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => cut062 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH062 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 1 1
    · exact presentation_entry_hasDerivAt b c d e U 1 2
    · exact presentation_entry_hasDerivAt b c d e U 1 3
    · exact presentation_entry_hasDerivAt b c d e U 1 4
    · exact presentation_entry_hasDerivAt b c d e U 1 5
  have hd : ∀ j : Fin 5, ((cut062 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD062 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => ((cut062 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD062 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge062_0] using (detJet060 b c d e U).1
    · simpa only [cutEdge062_1] using (detJet058 b c d e U).1
    · simpa only [cutEdge062_2] using (detJet054 b c d e U).1
    · simpa only [cutEdge062_3] using (detJet046 b c d e U).1
    · simpa only [cutEdge062_4] using (detJet030 b c d e U).1
  have hd' : ∀ j : Fin 5, HasDerivAt (fun T : ℂ => ((cut062 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ062 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin5 (P := fun j => HasDerivAt (fun T : ℂ => ((cut062 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ062 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge062_0] using (detJet060 b c d e U).2
    · simpa only [cutEdge062_1] using (detJet058 b c d e U).2
    · simpa only [cutEdge062_2] using (detJet054 b c d e U).2
    · simpa only [cutEdge062_3] using (detJet046 b c d e U).2
    · simpa only [cutEdge062_4] using (detJet030 b c d e U).2
  have step := det_row_zero_jet (n := 4) (fun T : ℂ => cut062 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA062 (point b c d e U)) (entriesH062 (point b c d e U)) (childD062 (point b c d e U)) (childJ062 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity062 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity062 (point b c d e U)).symm⟩
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
    (cut063 (N6.Resultant6General.presentation 0 b c d e U 0)).det = value (point b c d e U) D063 ∧
    HasDerivAt (fun T : ℂ => (cut063 (N6.Resultant6General.presentation 0 b c d e U T)).det) (value (point b c d e U) J063) 0 := by
  have he : ∀ j : Fin 6, cut063 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA063 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin6 (P := fun j => cut063 (N6.Resultant6General.presentation 0 b c d e U 0) 0 j = entriesA063 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_zero b c d e U 0 0
    · exact presentation_entry_zero b c d e U 0 1
    · exact presentation_entry_zero b c d e U 0 2
    · exact presentation_entry_zero b c d e U 0 3
    · exact presentation_entry_zero b c d e U 0 4
    · exact presentation_entry_zero b c d e U 0 5
  have he' : ∀ j : Fin 6, HasDerivAt (fun T : ℂ => cut063 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH063 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin6 (P := fun j => HasDerivAt (fun T : ℂ => cut063 (N6.Resultant6General.presentation 0 b c d e U T) 0 j) (entriesH063 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_ ?_
    · exact presentation_entry_hasDerivAt b c d e U 0 0
    · exact presentation_entry_hasDerivAt b c d e U 0 1
    · exact presentation_entry_hasDerivAt b c d e U 0 2
    · exact presentation_entry_hasDerivAt b c d e U 0 3
    · exact presentation_entry_hasDerivAt b c d e U 0 4
    · exact presentation_entry_hasDerivAt b c d e U 0 5
  have hd : ∀ j : Fin 6, ((cut063 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD063 (point b c d e U) j := by
    refine N6.ResultantMinors.JetFinite.forallFin6 (P := fun j => ((cut063 (N6.Resultant6General.presentation 0 b c d e U 0)).submatrix Fin.succ j.succAbove).det = childD063 (point b c d e U) j) ?_ ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge063_0] using (detJet062 b c d e U).1
    · simpa only [cutEdge063_1] using (detJet061 b c d e U).1
    · simpa only [cutEdge063_2] using (detJet059 b c d e U).1
    · simpa only [cutEdge063_3] using (detJet055 b c d e U).1
    · simpa only [cutEdge063_4] using (detJet047 b c d e U).1
    · simpa only [cutEdge063_5] using (detJet031 b c d e U).1
  have hd' : ∀ j : Fin 6, HasDerivAt (fun T : ℂ => ((cut063 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ063 (point b c d e U) j) 0 := by
    refine N6.ResultantMinors.JetFinite.forallFin6 (P := fun j => HasDerivAt (fun T : ℂ => ((cut063 (N6.Resultant6General.presentation 0 b c d e U T)).submatrix Fin.succ j.succAbove).det) (childJ063 (point b c d e U) j) 0) ?_ ?_ ?_ ?_ ?_ ?_
    · simpa only [cutEdge063_0] using (detJet062 b c d e U).2
    · simpa only [cutEdge063_1] using (detJet061 b c d e U).2
    · simpa only [cutEdge063_2] using (detJet059 b c d e U).2
    · simpa only [cutEdge063_3] using (detJet055 b c d e U).2
    · simpa only [cutEdge063_4] using (detJet047 b c d e U).2
    · simpa only [cutEdge063_5] using (detJet031 b c d e U).2
  have step := det_row_zero_jet (n := 5) (fun T : ℂ => cut063 (N6.Resultant6General.presentation 0 b c d e U T))
    (entriesA063 (point b c d e U)) (entriesH063 (point b c d e U)) (childD063 (point b c d e U)) (childJ063 (point b c d e U)) he he' hd hd'
  exact ⟨step.1.trans (const_identity063 (point b c d e U)).symm,
    step.2.congr_deriv (linear_identity063 (point b c d e U)).symm⟩
end N6.Exceptional
