import N6.Weighted49.GateGround001
import N6.Weighted49.FullColumnLayouts
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step016_vector : ∀ i : Fin 49, step016Left * vec_M017 i = step016Right * matVec matrix_k vec_M007 i := by
  intro i
  exact array_gate step016Left step016Right vec_M007Data vec_M017Data matrix_kColumns FullLists.k FullLists_k_layout rfl step016_list i
#print axioms step016_vector
theorem step017_vector : ∀ i : Fin 49, step017Left * vec_M018 i = step017Right * matVec matrix_e vec_M004 i := by
  intro i
  exact array_gate step017Left step017Right vec_M004Data vec_M018Data matrix_eColumns FullLists.e FullLists_e_layout rfl step017_list i
#print axioms step017_vector
theorem step018_vector : ∀ i : Fin 49, step018Left * vec_M019 i = step018Right * matVec matrix_e vec_M005 i := by
  intro i
  exact array_gate step018Left step018Right vec_M005Data vec_M019Data matrix_eColumns FullLists.e FullLists_e_layout rfl step018_list i
#print axioms step018_vector
theorem step019_vector : ∀ i : Fin 49, step019Left * vec_M020 i = step019Right * matVec matrix_e vec_M006 i := by
  intro i
  exact array_gate step019Left step019Right vec_M006Data vec_M020Data matrix_eColumns FullLists.e FullLists_e_layout rfl step019_list i
#print axioms step019_vector
theorem step020_vector : ∀ i : Fin 49, step020Left * vec_M021 i = step020Right * matVec matrix_e vec_M007 i := by
  intro i
  exact array_gate step020Left step020Right vec_M007Data vec_M021Data matrix_eColumns FullLists.e FullLists_e_layout rfl step020_list i
#print axioms step020_vector
theorem step021_vector : ∀ i : Fin 49, step021Left * vec_M022 i = step021Right * matVec matrix_e vec_M008 i := by
  intro i
  exact array_gate step021Left step021Right vec_M008Data vec_M022Data matrix_eColumns FullLists.e FullLists_e_layout rfl step021_list i
#print axioms step021_vector
theorem step022_vector : ∀ i : Fin 49, step022Left * vec_M023 i = step022Right * matVec matrix_e vec_M009 i := by
  intro i
  exact array_gate step022Left step022Right vec_M009Data vec_M023Data matrix_eColumns FullLists.e FullLists_e_layout rfl step022_list i
#print axioms step022_vector
theorem step023_vector : ∀ i : Fin 49, step023Left * vec_M024 i = step023Right * matVec matrix_e vec_M010 i := by
  intro i
  exact array_gate step023Left step023Right vec_M010Data vec_M024Data matrix_eColumns FullLists.e FullLists_e_layout rfl step023_list i
#print axioms step023_vector
theorem step024_vector : ∀ i : Fin 49, step024Left * vec_M025 i = step024Right * matVec matrix_B vec_M011 i := by
  intro i
  exact array_gate step024Left step024Right vec_M011Data vec_M025Data matrix_BColumns FullLists.B FullLists_B_layout rfl step024_list i
#print axioms step024_vector
theorem step025_vector : ∀ i : Fin 49, step025Left * vec_M026 i = step025Right * matVec matrix_c vec_M011 i := by
  intro i
  exact array_gate step025Left step025Right vec_M011Data vec_M026Data matrix_cColumns FullLists.c FullLists_c_layout rfl step025_list i
#print axioms step025_vector
theorem step026_vector : ∀ i : Fin 49, step026Left * vec_M027 i = step026Right * matVec matrix_c vec_M012 i := by
  intro i
  exact array_gate step026Left step026Right vec_M012Data vec_M027Data matrix_cColumns FullLists.c FullLists_c_layout rfl step026_list i
#print axioms step026_vector
theorem step027_vector : ∀ i : Fin 49, step027Left * vec_M028 i = step027Right * matVec matrix_c vec_M013 i := by
  intro i
  exact array_gate step027Left step027Right vec_M013Data vec_M028Data matrix_cColumns FullLists.c FullLists_c_layout rfl step027_list i
#print axioms step027_vector
theorem step028_vector : ∀ i : Fin 49, step028Left * vec_M029 i = step028Right * matVec matrix_c vec_M014 i := by
  intro i
  exact array_gate step028Left step028Right vec_M014Data vec_M029Data matrix_cColumns FullLists.c FullLists_c_layout rfl step028_list i
#print axioms step028_vector
theorem step029_vector : ∀ i : Fin 49, step029Left * vec_M030 i = step029Right * matVec matrix_k vec_M011 i := by
  intro i
  exact array_gate step029Left step029Right vec_M011Data vec_M030Data matrix_kColumns FullLists.k FullLists_k_layout rfl step029_list i
#print axioms step029_vector
theorem step030_vector : ∀ i : Fin 49, step030Left * vec_M031 i = step030Right * matVec matrix_k vec_M012 i := by
  intro i
  exact array_gate step030Left step030Right vec_M012Data vec_M031Data matrix_kColumns FullLists.k FullLists_k_layout rfl step030_list i
#print axioms step030_vector
theorem step031_vector : ∀ i : Fin 49, step031Left * vec_M032 i = step031Right * matVec matrix_k vec_M013 i := by
  intro i
  exact array_gate step031Left step031Right vec_M013Data vec_M032Data matrix_kColumns FullLists.k FullLists_k_layout rfl step031_list i
#print axioms step031_vector
end N6.Weighted49
