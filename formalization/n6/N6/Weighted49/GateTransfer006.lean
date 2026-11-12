import N6.Weighted49.GateGround006
import N6.Weighted49.FullColumnLayouts
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step096_vector : ∀ i : Fin 49, step096Left * vec_M097 i = step096Right * matVec matrix_e vec_M055 i := by
  intro i
  exact array_gate step096Left step096Right vec_M055Data vec_M097Data matrix_eColumns FullLists.e FullLists_e_layout rfl step096_list i
#print axioms step096_vector
theorem step097_vector : ∀ i : Fin 49, step097Left * vec_M098 i = step097Right * matVec matrix_e vec_M056 i := by
  intro i
  exact array_gate step097Left step097Right vec_M056Data vec_M098Data matrix_eColumns FullLists.e FullLists_e_layout rfl step097_list i
#print axioms step097_vector
theorem step098_vector : ∀ i : Fin 49, step098Left * vec_M099 i = step098Right * matVec matrix_e vec_M057 i := by
  intro i
  exact array_gate step098Left step098Right vec_M057Data vec_M099Data matrix_eColumns FullLists.e FullLists_e_layout rfl step098_list i
#print axioms step098_vector
theorem step099_vector : ∀ i : Fin 49, step099Left * vec_M100 i = step099Right * matVec matrix_e vec_M058 i := by
  intro i
  exact array_gate step099Left step099Right vec_M058Data vec_M100Data matrix_eColumns FullLists.e FullLists_e_layout rfl step099_list i
#print axioms step099_vector
theorem step100_vector : ∀ i : Fin 49, step100Left * vec_M101 i = step100Right * matVec matrix_e vec_M059 i := by
  intro i
  exact array_gate step100Left step100Right vec_M059Data vec_M101Data matrix_eColumns FullLists.e FullLists_e_layout rfl step100_list i
#print axioms step100_vector
theorem step101_vector : ∀ i : Fin 49, step101Left * vec_M102 i = step101Right * matVec matrix_e vec_M060 i := by
  intro i
  exact array_gate step101Left step101Right vec_M060Data vec_M102Data matrix_eColumns FullLists.e FullLists_e_layout rfl step101_list i
#print axioms step101_vector
theorem step102_vector : ∀ i : Fin 49, step102Left * vec_M103 i = step102Right * matVec matrix_e vec_M061 i := by
  intro i
  exact array_gate step102Left step102Right vec_M061Data vec_M103Data matrix_eColumns FullLists.e FullLists_e_layout rfl step102_list i
#print axioms step102_vector
theorem step103_vector : ∀ i : Fin 49, step103Left * vec_M104 i = step103Right * matVec matrix_e vec_M062 i := by
  intro i
  exact array_gate step103Left step103Right vec_M062Data vec_M104Data matrix_eColumns FullLists.e FullLists_e_layout rfl step103_list i
#print axioms step103_vector
theorem step104_vector : ∀ i : Fin 49, step104Left * vec_M105 i = step104Right * matVec matrix_e vec_M063 i := by
  intro i
  exact array_gate step104Left step104Right vec_M063Data vec_M105Data matrix_eColumns FullLists.e FullLists_e_layout rfl step104_list i
#print axioms step104_vector
theorem step105_vector : ∀ i : Fin 49, step105Left * vec_M106 i = step105Right * matVec matrix_e vec_M064 i := by
  intro i
  exact array_gate step105Left step105Right vec_M064Data vec_M106Data matrix_eColumns FullLists.e FullLists_e_layout rfl step105_list i
#print axioms step105_vector
theorem step106_vector : ∀ i : Fin 49, step106Left * vec_M107 i = step106Right * matVec matrix_e vec_M065 i := by
  intro i
  exact array_gate step106Left step106Right vec_M065Data vec_M107Data matrix_eColumns FullLists.e FullLists_e_layout rfl step106_list i
#print axioms step106_vector
theorem step107_vector : ∀ i : Fin 49, step107Left * vec_M108 i = step107Right * matVec matrix_e vec_M066 i := by
  intro i
  exact array_gate step107Left step107Right vec_M066Data vec_M108Data matrix_eColumns FullLists.e FullLists_e_layout rfl step107_list i
#print axioms step107_vector
theorem step108_vector : ∀ i : Fin 49, step108Left * vec_M109 i = step108Right * matVec matrix_e vec_M070 i := by
  intro i
  exact array_gate step108Left step108Right vec_M070Data vec_M109Data matrix_eColumns FullLists.e FullLists_e_layout rfl step108_list i
#print axioms step108_vector
theorem step109_vector : ∀ i : Fin 49, step109Left * vec_M110 i = step109Right * matVec matrix_e vec_M072 i := by
  intro i
  exact array_gate step109Left step109Right vec_M072Data vec_M110Data matrix_eColumns FullLists.e FullLists_e_layout rfl step109_list i
#print axioms step109_vector
theorem step110_vector : ∀ i : Fin 49, step110Left * vec_M111 i = step110Right * matVec matrix_e vec_M073 i := by
  intro i
  exact array_gate step110Left step110Right vec_M073Data vec_M111Data matrix_eColumns FullLists.e FullLists_e_layout rfl step110_list i
#print axioms step110_vector
theorem step111_vector : ∀ i : Fin 49, step111Left * vec_M112 i = step111Right * matVec matrix_k vec_M081 i := by
  intro i
  exact array_gate step111Left step111Right vec_M081Data vec_M112Data matrix_kColumns FullLists.k FullLists_k_layout rfl step111_list i
#print axioms step111_vector
end N6.Weighted49
