import N6.Weighted49.GateGround003
import N6.Weighted49.FullColumnLayouts
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step048_vector : ∀ i : Fin 49, step048Left * vec_M049 i = step048Right * matVec matrix_c vec_M026 i := by
  intro i
  exact array_gate step048Left step048Right vec_M026Data vec_M049Data matrix_cColumns FullLists.c FullLists_c_layout rfl step048_list i
#print axioms step048_vector
theorem step049_vector : ∀ i : Fin 49, step049Left * vec_M050 i = step049Right * matVec matrix_c vec_M027 i := by
  intro i
  exact array_gate step049Left step049Right vec_M027Data vec_M050Data matrix_cColumns FullLists.c FullLists_c_layout rfl step049_list i
#print axioms step049_vector
theorem step050_vector : ∀ i : Fin 49, step050Left * vec_M051 i = step050Right * matVec matrix_c vec_M028 i := by
  intro i
  exact array_gate step050Left step050Right vec_M028Data vec_M051Data matrix_cColumns FullLists.c FullLists_c_layout rfl step050_list i
#print axioms step050_vector
theorem step051_vector : ∀ i : Fin 49, step051Left * vec_M052 i = step051Right * matVec matrix_c vec_M029 i := by
  intro i
  exact array_gate step051Left step051Right vec_M029Data vec_M052Data matrix_cColumns FullLists.c FullLists_c_layout rfl step051_list i
#print axioms step051_vector
theorem step052_vector : ∀ i : Fin 49, step052Left * vec_M053 i = step052Right * matVec matrix_k vec_M025 i := by
  intro i
  exact array_gate step052Left step052Right vec_M025Data vec_M053Data matrix_kColumns FullLists.k FullLists_k_layout rfl step052_list i
#print axioms step052_vector
theorem step053_vector : ∀ i : Fin 49, step053Left * vec_M054 i = step053Right * matVec matrix_k vec_M026 i := by
  intro i
  exact array_gate step053Left step053Right vec_M026Data vec_M054Data matrix_kColumns FullLists.k FullLists_k_layout rfl step053_list i
#print axioms step053_vector
theorem step054_vector : ∀ i : Fin 49, step054Left * vec_M055 i = step054Right * matVec matrix_k vec_M027 i := by
  intro i
  exact array_gate step054Left step054Right vec_M027Data vec_M055Data matrix_kColumns FullLists.k FullLists_k_layout rfl step054_list i
#print axioms step054_vector
theorem step055_vector : ∀ i : Fin 49, step055Left * vec_M056 i = step055Right * matVec matrix_k vec_M028 i := by
  intro i
  exact array_gate step055Left step055Right vec_M028Data vec_M056Data matrix_kColumns FullLists.k FullLists_k_layout rfl step055_list i
#print axioms step055_vector
theorem step056_vector : ∀ i : Fin 49, step056Left * vec_M057 i = step056Right * matVec matrix_k vec_M030 i := by
  intro i
  exact array_gate step056Left step056Right vec_M030Data vec_M057Data matrix_kColumns FullLists.k FullLists_k_layout rfl step056_list i
#print axioms step056_vector
theorem step057_vector : ∀ i : Fin 49, step057Left * vec_M058 i = step057Right * matVec matrix_k vec_M031 i := by
  intro i
  exact array_gate step057Left step057Right vec_M031Data vec_M058Data matrix_kColumns FullLists.k FullLists_k_layout rfl step057_list i
#print axioms step057_vector
theorem step058_vector : ∀ i : Fin 49, step058Left * vec_M059 i = step058Right * matVec matrix_k vec_M032 i := by
  intro i
  exact array_gate step058Left step058Right vec_M032Data vec_M059Data matrix_kColumns FullLists.k FullLists_k_layout rfl step058_list i
#print axioms step058_vector
theorem step059_vector : ∀ i : Fin 49, step059Left * vec_M060 i = step059Right * matVec matrix_k vec_M033 i := by
  intro i
  exact array_gate step059Left step059Right vec_M033Data vec_M060Data matrix_kColumns FullLists.k FullLists_k_layout rfl step059_list i
#print axioms step059_vector
theorem step060_vector : ∀ i : Fin 49, step060Left * vec_M061 i = step060Right * matVec matrix_e vec_M028 i := by
  intro i
  exact array_gate step060Left step060Right vec_M028Data vec_M061Data matrix_eColumns FullLists.e FullLists_e_layout rfl step060_list i
#print axioms step060_vector
theorem step061_vector : ∀ i : Fin 49, step061Left * vec_M062 i = step061Right * matVec matrix_e vec_M029 i := by
  intro i
  exact array_gate step061Left step061Right vec_M029Data vec_M062Data matrix_eColumns FullLists.e FullLists_e_layout rfl step061_list i
#print axioms step061_vector
theorem step062_vector : ∀ i : Fin 49, step062Left * vec_M063 i = step062Right * matVec matrix_e vec_M031 i := by
  intro i
  exact array_gate step062Left step062Right vec_M031Data vec_M063Data matrix_eColumns FullLists.e FullLists_e_layout rfl step062_list i
#print axioms step062_vector
theorem step063_vector : ∀ i : Fin 49, step063Left * vec_M064 i = step063Right * matVec matrix_e vec_M032 i := by
  intro i
  exact array_gate step063Left step063Right vec_M032Data vec_M064Data matrix_eColumns FullLists.e FullLists_e_layout rfl step063_list i
#print axioms step063_vector
end N6.Weighted49
