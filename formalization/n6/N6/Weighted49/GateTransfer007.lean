import N6.Weighted49.GateGround007
import N6.Weighted49.FullColumnLayouts
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step112_vector : ∀ i : Fin 49, step112Left * vec_M113 i = step112Right * matVec matrix_k vec_M083 i := by
  intro i
  exact array_gate step112Left step112Right vec_M083Data vec_M113Data matrix_kColumns FullLists.k FullLists_k_layout rfl step112_list i
#print axioms step112_vector
theorem step113_vector : ∀ i : Fin 49, step113Left * vec_M114 i = step113Right * matVec matrix_k vec_M084 i := by
  intro i
  exact array_gate step113Left step113Right vec_M084Data vec_M114Data matrix_kColumns FullLists.k FullLists_k_layout rfl step113_list i
#print axioms step113_vector
theorem step114_vector : ∀ i : Fin 49, step114Left * vec_M115 i = step114Right * matVec matrix_k vec_M085 i := by
  intro i
  exact array_gate step114Left step114Right vec_M085Data vec_M115Data matrix_kColumns FullLists.k FullLists_k_layout rfl step114_list i
#print axioms step114_vector
theorem step115_vector : ∀ i : Fin 49, step115Left * vec_M116 i = step115Right * matVec matrix_k vec_M086 i := by
  intro i
  exact array_gate step115Left step115Right vec_M086Data vec_M116Data matrix_kColumns FullLists.k FullLists_k_layout rfl step115_list i
#print axioms step115_vector
theorem step116_vector : ∀ i : Fin 49, step116Left * vec_M117 i = step116Right * matVec matrix_k vec_M087 i := by
  intro i
  exact array_gate step116Left step116Right vec_M087Data vec_M117Data matrix_kColumns FullLists.k FullLists_k_layout rfl step116_list i
#print axioms step116_vector
theorem step117_vector : ∀ i : Fin 49, step117Left * vec_M118 i = step117Right * matVec matrix_k vec_M088 i := by
  intro i
  exact array_gate step117Left step117Right vec_M088Data vec_M118Data matrix_kColumns FullLists.k FullLists_k_layout rfl step117_list i
#print axioms step117_vector
theorem step118_vector : ∀ i : Fin 49, step118Left * vec_M119 i = step118Right * matVec matrix_k vec_M090 i := by
  intro i
  exact array_gate step118Left step118Right vec_M090Data vec_M119Data matrix_kColumns FullLists.k FullLists_k_layout rfl step118_list i
#print axioms step118_vector
theorem step119_vector : ∀ i : Fin 49, step119Left * vec_M120 i = step119Right * matVec matrix_k vec_M091 i := by
  intro i
  exact array_gate step119Left step119Right vec_M091Data vec_M120Data matrix_kColumns FullLists.k FullLists_k_layout rfl step119_list i
#print axioms step119_vector
theorem step120_vector : ∀ i : Fin 49, step120Left * vec_M121 i = step120Right * matVec matrix_e vec_M082 i := by
  intro i
  exact array_gate step120Left step120Right vec_M082Data vec_M121Data matrix_eColumns FullLists.e FullLists_e_layout rfl step120_list i
#print axioms step120_vector
theorem step121_vector : ∀ i : Fin 49, step121Left * vec_M122 i = step121Right * matVec matrix_e vec_M085 i := by
  intro i
  exact array_gate step121Left step121Right vec_M085Data vec_M122Data matrix_eColumns FullLists.e FullLists_e_layout rfl step121_list i
#print axioms step121_vector
theorem step122_vector : ∀ i : Fin 49, step122Left * vec_M123 i = step122Right * matVec matrix_e vec_M088 i := by
  intro i
  exact array_gate step122Left step122Right vec_M088Data vec_M123Data matrix_eColumns FullLists.e FullLists_e_layout rfl step122_list i
#print axioms step122_vector
theorem step123_vector : ∀ i : Fin 49, step123Left * vec_M124 i = step123Right * matVec matrix_e vec_M089 i := by
  intro i
  exact array_gate step123Left step123Right vec_M089Data vec_M124Data matrix_eColumns FullLists.e FullLists_e_layout rfl step123_list i
#print axioms step123_vector
theorem step124_vector : ∀ i : Fin 49, step124Left * vec_M125 i = step124Right * matVec matrix_e vec_M090 i := by
  intro i
  exact array_gate step124Left step124Right vec_M090Data vec_M125Data matrix_eColumns FullLists.e FullLists_e_layout rfl step124_list i
#print axioms step124_vector
theorem step125_vector : ∀ i : Fin 49, step125Left * vec_M126 i = step125Right * matVec matrix_e vec_M091 i := by
  intro i
  exact array_gate step125Left step125Right vec_M091Data vec_M126Data matrix_eColumns FullLists.e FullLists_e_layout rfl step125_list i
#print axioms step125_vector
theorem step126_vector : ∀ i : Fin 49, step126Left * vec_M127 i = step126Right * matVec matrix_e vec_M092 i := by
  intro i
  exact array_gate step126Left step126Right vec_M092Data vec_M127Data matrix_eColumns FullLists.e FullLists_e_layout rfl step126_list i
#print axioms step126_vector
theorem step127_vector : ∀ i : Fin 49, step127Left * vec_M128 i = step127Right * matVec matrix_e vec_M101 i := by
  intro i
  exact array_gate step127Left step127Right vec_M101Data vec_M128Data matrix_eColumns FullLists.e FullLists_e_layout rfl step127_list i
#print axioms step127_vector
end N6.Weighted49
