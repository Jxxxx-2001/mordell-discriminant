import N6.Weighted49.KrylovGate004
import N6.Weighted49.WeightedCoordinates
import N6.Weighted49.LexSemantics
import N6.Weighted49.RowTransfer_P35
import N6.Weighted49.RowTransfer_c
import N6.Weighted49.RowTransfer_k
import N6.Weighted49.RowTransfer_e
import N6.Weighted49.ActionsFromInputs
import Mathlib.Data.Fintype.Fin
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
open scoped BigOperators
theorem P35_from_actions {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0) :
    globalP35 (x 4) = 0 := by
  have sources : ∀ j : Fin 36, W (fun i => value x (basisData i)) (row_P35Source j) = (row_P35Dens j : R)*(value x N6.Dcolon1.dData * row_P35Mon x j) := by
    intro j
    fin_cases j
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using D_initialization x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K001 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K002 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K003 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K004 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K005 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K006 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K007 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K008 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K009 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K010 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K011 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K012 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K013 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K014 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K015 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K016 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K017 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K018 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K019 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K020 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K021 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K022 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K023 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K024 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K025 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K026 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K027 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K028 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K029 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K030 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K031 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K032 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K033 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K034 x hWA
    · simpa only [row_P35Source, row_P35Dens, row_P35Mon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K035 x hWA
  have h := cancel_weighted_row (fun i => value x (basisData i)) row_P35Weights row_P35Dens row_P35Coefficients row_P35Source (row_P35Mon x) row_P35Gcd row_P35L (x 0) (x 4) (value x N6.Dcolon1.dData) row_P35L_nonzero hs row_P35ZeroChecked row_P35WeightsChecked sources
  simpa only [globalP35, row_P35Mon] using h
#print axioms P35_from_actions
theorem c_from_actions {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0) :
    coordinate_c (x 4) (x 3) = 0 := by
  have sources : ∀ j : Fin 36, W (fun i => value x (basisData i)) (row_cSource j) = (row_cDens j : R)*(value x N6.Dcolon1.dData * row_cMon x j) := by
    intro j
    fin_cases j
    · change W (fun i => value x (basisData i)) vec_K000 = (den_K000 : R)*(value x N6.Dcolon1.dData * x 4 ^ 0)
      simpa only [pow_zero, mul_one] using D_initialization x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K001 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K002 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K003 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K004 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K005 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K006 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K007 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K008 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K009 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K010 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K011 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K012 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K013 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K014 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K015 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K016 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K017 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K018 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K019 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K020 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K021 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K022 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K023 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K024 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K025 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K026 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K027 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K028 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K029 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K030 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K031 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K032 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K033 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K034 x hWA
    · simpa only [row_cSource, row_cDens, row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using weighted_c x hWA
  have h := cancel_weighted_row (fun i => value x (basisData i)) row_cWeights row_cDens row_cCoefficients row_cSource (row_cMon x) row_cGcd row_cL (x 0) (x 4) (value x N6.Dcolon1.dData) row_cL_nonzero hs row_cZeroChecked row_cWeightsChecked sources
  rw [Fin.sum_univ_castSucc] at h
  simp only [row_cMon, Fin.lastCases_castSucc, Fin.lastCases_last, row_cCoeffCastSucc, row_cCoeffLast] at h
  simpa only [coordinate_c, add_comm] using h
#print axioms c_from_actions
theorem k_from_actions {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0) :
    coordinate_k (x 4) (x 2) = 0 := by
  have sources : ∀ j : Fin 36, W (fun i => value x (basisData i)) (row_kSource j) = (row_kDens j : R)*(value x N6.Dcolon1.dData * row_kMon x j) := by
    intro j
    fin_cases j
    · change W (fun i => value x (basisData i)) vec_K000 = (den_K000 : R)*(value x N6.Dcolon1.dData * x 4 ^ 0)
      simpa only [pow_zero, mul_one] using D_initialization x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K001 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K002 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K003 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K004 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K005 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K006 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K007 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K008 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K009 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K010 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K011 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K012 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K013 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K014 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K015 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K016 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K017 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K018 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K019 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K020 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K021 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K022 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K023 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K024 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K025 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K026 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K027 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K028 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K029 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K030 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K031 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K032 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K033 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K034 x hWA
    · simpa only [row_kSource, row_kDens, row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using weighted_k x hWA
  have h := cancel_weighted_row (fun i => value x (basisData i)) row_kWeights row_kDens row_kCoefficients row_kSource (row_kMon x) row_kGcd row_kL (x 0) (x 4) (value x N6.Dcolon1.dData) row_kL_nonzero hs row_kZeroChecked row_kWeightsChecked sources
  rw [Fin.sum_univ_castSucc] at h
  simp only [row_kMon, Fin.lastCases_castSucc, Fin.lastCases_last, row_kCoeffCastSucc, row_kCoeffLast] at h
  simpa only [coordinate_k, add_comm] using h
#print axioms k_from_actions
theorem e_from_actions {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (hWA : ∀ i : Fin 49, value x (actionData i) = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0) :
    coordinate_e (x 4) (x 1) = 0 := by
  have sources : ∀ j : Fin 36, W (fun i => value x (basisData i)) (row_eSource j) = (row_eDens j : R)*(value x N6.Dcolon1.dData * row_eMon x j) := by
    intro j
    fin_cases j
    · change W (fun i => value x (basisData i)) vec_K000 = (den_K000 : R)*(value x N6.Dcolon1.dData * x 4 ^ 0)
      simpa only [pow_zero, mul_one] using D_initialization x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K001 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K002 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K003 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K004 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K005 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K006 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K007 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K008 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K009 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K010 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K011 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K012 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K013 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K014 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K015 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K016 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K017 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K018 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K019 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K020 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K021 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K022 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K023 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K024 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K025 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K026 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K027 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K028 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K029 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K030 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K031 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K032 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K033 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using krylov_K034 x hWA
    · simpa only [row_eSource, row_eDens, row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, Fin.val_castSucc, pow_zero, mul_one] using weighted_e x hWA
  have h := cancel_weighted_row (fun i => value x (basisData i)) row_eWeights row_eDens row_eCoefficients row_eSource (row_eMon x) row_eGcd row_eL (x 0) (x 4) (value x N6.Dcolon1.dData) row_eL_nonzero hs row_eZeroChecked row_eWeightsChecked sources
  rw [Fin.sum_univ_castSucc] at h
  simp only [row_eMon, Fin.lastCases_castSucc, Fin.lastCases_last, row_eCoeffCastSucc, row_eCoeffLast] at h
  simpa only [coordinate_e, add_comm] using h
#print axioms e_from_actions
theorem cover_from_inputs {R : Type*} [CommRing R] [Algebra ℚ R] (x : Fin 5 → R)
    (h0 : value x N6.Dcolon1.f0Data = 0)
    (h1 : value x N6.Dcolon1.f1Data = 0)
    (h2 : value x N6.Dcolon1.f2Data = 0)
    (h3 : value x N6.Dcolon1.f3Data = 0)
    (hs : x 0 * x 4 * value x N6.Dcolon1.dData - 1 = 0)
    : globalP35 (x 4) = 0 ∧ coordinate_c (x 4) (x 3) = 0 ∧ coordinate_k (x 4) (x 2) = 0 ∧ coordinate_e (x 4) (x 1) = 0 := by
  have hWA := all_actions_from_inputs x h0 h1 h2 h3 hs
  exact ⟨P35_from_actions x hWA hs, c_from_actions x hWA hs, k_from_actions x hWA hs, e_from_actions x hWA hs⟩
#print axioms cover_from_inputs
end N6.Weighted49
