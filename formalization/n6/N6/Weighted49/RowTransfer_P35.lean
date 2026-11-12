import N6.Weighted49.RowGround_P35
import N6.Weighted49.ArithmeticFoldSemantics
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem row_P35ZeroChecked : ∀ i : Fin 49, sumInt (fun j : Fin 36 => row_P35Weights j * row_P35Source j i) = 0 := by
  intro i
  have h := congrArg (fun xs : List Int => xs.getD i.val 0) row_P35ZeroListChecked
  dsimp only at h
  rw [getD_foldColumns] at h
  simp only [row_P35ColumnsList, getD_columnLists, getD_arrayList] at h
  change sumInt (fun j : Fin 36 => row_P35Source j i * row_P35Weights j) = (List.replicate 49 (0 : Int)).getD i.val 0 at h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq] at h
  simpa only [mul_comm] using h
#print axioms row_P35ZeroChecked
end N6.Weighted49
