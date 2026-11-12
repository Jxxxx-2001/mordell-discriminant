import N6.Weighted49.InitGround
import N6.Weighted49.ArithmeticFoldSemantics
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem initVectorChecked : ∀ i : Fin 49, step136Left * vec_K000 i = sumInt (fun j : Fin 76 => initWeights j * initSource j i) := by
  intro i
  have h := congrArg (fun xs : List Int => xs.getD i.val 0) initListChecked
  dsimp only at h
  rw [getD_scaleList, getD_foldColumns] at h
  simp only [initColumnsList, getD_columnLists, getD_arrayList] at h
  change step136Left * vec_K000 i = sumInt (fun j : Fin 76 => initSource j i * initWeights j) at h
  simpa only [mul_comm] using h
#print axioms initVectorChecked
end N6.Weighted49
