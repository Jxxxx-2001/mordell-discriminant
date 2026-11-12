import N6.Weighted49.RowGround_e
import N6.Weighted49.ArithmeticFoldSemantics
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem row_eZeroChecked : ∀ i : Fin 49, sumInt (fun j : Fin 36 => row_eWeights j * row_eSource j i) = 0 := by
  intro i
  have h := congrArg (fun xs : List Int => xs.getD i.val 0) row_eZeroListChecked
  dsimp only at h
  rw [getD_foldColumns] at h
  simp only [row_eColumnsList, getD_columnLists, getD_arrayList] at h
  change sumInt (fun j : Fin 36 => row_eSource j i * row_eWeights j) = (List.replicate 49 (0 : Int)).getD i.val 0 at h
  simp only [List.getD_eq_getElem?_getD, List.getElem?_getD_replicate_default_eq] at h
  simpa only [mul_comm] using h
#print axioms row_eZeroChecked
end N6.Weighted49
