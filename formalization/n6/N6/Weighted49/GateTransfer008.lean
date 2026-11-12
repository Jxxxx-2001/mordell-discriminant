import N6.Weighted49.GateGround008
import N6.Weighted49.FullColumnLayouts
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step128_vector : ∀ i : Fin 49, step128Left * vec_M129 i = step128Right * matVec matrix_e vec_M102 i := by
  intro i
  exact array_gate step128Left step128Right vec_M102Data vec_M129Data matrix_eColumns FullLists.e FullLists_e_layout rfl step128_list i
#print axioms step128_vector
theorem step129_vector : ∀ i : Fin 49, step129Left * vec_M130 i = step129Right * matVec matrix_k vec_M112 i := by
  intro i
  exact array_gate step129Left step129Right vec_M112Data vec_M130Data matrix_kColumns FullLists.k FullLists_k_layout rfl step129_list i
#print axioms step129_vector
theorem step130_vector : ∀ i : Fin 49, step130Left * vec_M131 i = step130Right * matVec matrix_k vec_M114 i := by
  intro i
  exact array_gate step130Left step130Right vec_M114Data vec_M131Data matrix_kColumns FullLists.k FullLists_k_layout rfl step130_list i
#print axioms step130_vector
theorem step131_vector : ∀ i : Fin 49, step131Left * vec_M132 i = step131Right * matVec matrix_k vec_M117 i := by
  intro i
  exact array_gate step131Left step131Right vec_M117Data vec_M132Data matrix_kColumns FullLists.k FullLists_k_layout rfl step131_list i
#print axioms step131_vector
theorem step132_vector : ∀ i : Fin 49, step132Left * vec_M133 i = step132Right * matVec matrix_k vec_M118 i := by
  intro i
  exact array_gate step132Left step132Right vec_M118Data vec_M133Data matrix_kColumns FullLists.k FullLists_k_layout rfl step132_list i
#print axioms step132_vector
theorem step133_vector : ∀ i : Fin 49, step133Left * vec_M134 i = step133Right * matVec matrix_k vec_M119 i := by
  intro i
  exact array_gate step133Left step133Right vec_M119Data vec_M134Data matrix_kColumns FullLists.k FullLists_k_layout rfl step133_list i
#print axioms step133_vector
theorem step134_vector : ∀ i : Fin 49, step134Left * vec_M135 i = step134Right * matVec matrix_e vec_M120 i := by
  intro i
  exact array_gate step134Left step134Right vec_M120Data vec_M135Data matrix_eColumns FullLists.e FullLists_e_layout rfl step134_list i
#print axioms step134_vector
theorem step135_vector : ∀ i : Fin 49, step135Left * vec_M136 i = step135Right * matVec matrix_k vec_M134 i := by
  intro i
  exact array_gate step135Left step135Right vec_M134Data vec_M136Data matrix_kColumns FullLists.k FullLists_k_layout rfl step135_list i
#print axioms step135_vector
theorem step137_vector : ∀ i : Fin 49, step137Left * vec_D_c i = step137Right * matVec matrix_c vec_K000 i := by
  intro i
  exact array_gate step137Left step137Right vec_K000Data vec_D_cData matrix_cColumns FullLists.c FullLists_c_layout rfl step137_list i
#print axioms step137_vector
theorem step138_vector : ∀ i : Fin 49, step138Left * vec_D_k i = step138Right * matVec matrix_k vec_K000 i := by
  intro i
  exact array_gate step138Left step138Right vec_K000Data vec_D_kData matrix_kColumns FullLists.k FullLists_k_layout rfl step138_list i
#print axioms step138_vector
theorem step139_vector : ∀ i : Fin 49, step139Left * vec_D_e i = step139Right * matVec matrix_e vec_K000 i := by
  intro i
  exact array_gate step139Left step139Right vec_K000Data vec_D_eData matrix_eColumns FullLists.e FullLists_e_layout rfl step139_list i
#print axioms step139_vector
theorem step140_vector : ∀ i : Fin 49, step140Left * vec_K001 i = step140Right * matVec matrix_B vec_K000 i := by
  intro i
  exact array_gate step140Left step140Right vec_K000Data vec_K001Data matrix_BColumns FullLists.B FullLists_B_layout rfl step140_list i
#print axioms step140_vector
theorem step141_vector : ∀ i : Fin 49, step141Left * vec_K002 i = step141Right * matVec matrix_B vec_K001 i := by
  intro i
  exact array_gate step141Left step141Right vec_K001Data vec_K002Data matrix_BColumns FullLists.B FullLists_B_layout rfl step141_list i
#print axioms step141_vector
theorem step142_vector : ∀ i : Fin 49, step142Left * vec_K003 i = step142Right * matVec matrix_B vec_K002 i := by
  intro i
  exact array_gate step142Left step142Right vec_K002Data vec_K003Data matrix_BColumns FullLists.B FullLists_B_layout rfl step142_list i
#print axioms step142_vector
theorem step143_vector : ∀ i : Fin 49, step143Left * vec_K004 i = step143Right * matVec matrix_B vec_K003 i := by
  intro i
  exact array_gate step143Left step143Right vec_K003Data vec_K004Data matrix_BColumns FullLists.B FullLists_B_layout rfl step143_list i
#print axioms step143_vector
theorem step144_vector : ∀ i : Fin 49, step144Left * vec_K005 i = step144Right * matVec matrix_B vec_K004 i := by
  intro i
  exact array_gate step144Left step144Right vec_K004Data vec_K005Data matrix_BColumns FullLists.B FullLists_B_layout rfl step144_list i
#print axioms step144_vector
end N6.Weighted49
