import N6.Weighted49.GateGround002
import N6.Weighted49.FullColumnLayouts
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step032_vector : ∀ i : Fin 49, step032Left * vec_M033 i = step032Right * matVec matrix_k vec_M015 i := by
  intro i
  exact array_gate step032Left step032Right vec_M015Data vec_M033Data matrix_kColumns FullLists.k FullLists_k_layout rfl step032_list i
#print axioms step032_vector
theorem step033_vector : ∀ i : Fin 49, step033Left * vec_M034 i = step033Right * matVec matrix_k vec_M016 i := by
  intro i
  exact array_gate step033Left step033Right vec_M016Data vec_M034Data matrix_kColumns FullLists.k FullLists_k_layout rfl step033_list i
#print axioms step033_vector
theorem step034_vector : ∀ i : Fin 49, step034Left * vec_M035 i = step034Right * matVec matrix_e vec_M011 i := by
  intro i
  exact array_gate step034Left step034Right vec_M011Data vec_M035Data matrix_eColumns FullLists.e FullLists_e_layout rfl step034_list i
#print axioms step034_vector
theorem step035_vector : ∀ i : Fin 49, step035Left * vec_M036 i = step035Right * matVec matrix_e vec_M012 i := by
  intro i
  exact array_gate step035Left step035Right vec_M012Data vec_M036Data matrix_eColumns FullLists.e FullLists_e_layout rfl step035_list i
#print axioms step035_vector
theorem step036_vector : ∀ i : Fin 49, step036Left * vec_M037 i = step036Right * matVec matrix_e vec_M013 i := by
  intro i
  exact array_gate step036Left step036Right vec_M013Data vec_M037Data matrix_eColumns FullLists.e FullLists_e_layout rfl step036_list i
#print axioms step036_vector
theorem step037_vector : ∀ i : Fin 49, step037Left * vec_M038 i = step037Right * matVec matrix_e vec_M014 i := by
  intro i
  exact array_gate step037Left step037Right vec_M014Data vec_M038Data matrix_eColumns FullLists.e FullLists_e_layout rfl step037_list i
#print axioms step037_vector
theorem step038_vector : ∀ i : Fin 49, step038Left * vec_M039 i = step038Right * matVec matrix_e vec_M015 i := by
  intro i
  exact array_gate step038Left step038Right vec_M015Data vec_M039Data matrix_eColumns FullLists.e FullLists_e_layout rfl step038_list i
#print axioms step038_vector
theorem step039_vector : ∀ i : Fin 49, step039Left * vec_M040 i = step039Right * matVec matrix_e vec_M016 i := by
  intro i
  exact array_gate step039Left step039Right vec_M016Data vec_M040Data matrix_eColumns FullLists.e FullLists_e_layout rfl step039_list i
#print axioms step039_vector
theorem step040_vector : ∀ i : Fin 49, step040Left * vec_M041 i = step040Right * matVec matrix_e vec_M017 i := by
  intro i
  exact array_gate step040Left step040Right vec_M017Data vec_M041Data matrix_eColumns FullLists.e FullLists_e_layout rfl step040_list i
#print axioms step040_vector
theorem step041_vector : ∀ i : Fin 49, step041Left * vec_M042 i = step041Right * matVec matrix_e vec_M018 i := by
  intro i
  exact array_gate step041Left step041Right vec_M018Data vec_M042Data matrix_eColumns FullLists.e FullLists_e_layout rfl step041_list i
#print axioms step041_vector
theorem step042_vector : ∀ i : Fin 49, step042Left * vec_M043 i = step042Right * matVec matrix_e vec_M019 i := by
  intro i
  exact array_gate step042Left step042Right vec_M019Data vec_M043Data matrix_eColumns FullLists.e FullLists_e_layout rfl step042_list i
#print axioms step042_vector
theorem step043_vector : ∀ i : Fin 49, step043Left * vec_M044 i = step043Right * matVec matrix_e vec_M020 i := by
  intro i
  exact array_gate step043Left step043Right vec_M020Data vec_M044Data matrix_eColumns FullLists.e FullLists_e_layout rfl step043_list i
#print axioms step043_vector
theorem step044_vector : ∀ i : Fin 49, step044Left * vec_M045 i = step044Right * matVec matrix_e vec_M021 i := by
  intro i
  exact array_gate step044Left step044Right vec_M021Data vec_M045Data matrix_eColumns FullLists.e FullLists_e_layout rfl step044_list i
#print axioms step044_vector
theorem step045_vector : ∀ i : Fin 49, step045Left * vec_M046 i = step045Right * matVec matrix_e vec_M022 i := by
  intro i
  exact array_gate step045Left step045Right vec_M022Data vec_M046Data matrix_eColumns FullLists.e FullLists_e_layout rfl step045_list i
#print axioms step045_vector
theorem step046_vector : ∀ i : Fin 49, step046Left * vec_M047 i = step046Right * matVec matrix_e vec_M023 i := by
  intro i
  exact array_gate step046Left step046Right vec_M023Data vec_M047Data matrix_eColumns FullLists.e FullLists_e_layout rfl step046_list i
#print axioms step046_vector
theorem step047_vector : ∀ i : Fin 49, step047Left * vec_M048 i = step047Right * matVec matrix_e vec_M024 i := by
  intro i
  exact array_gate step047Left step047Right vec_M024Data vec_M048Data matrix_eColumns FullLists.e FullLists_e_layout rfl step047_list i
#print axioms step047_vector
end N6.Weighted49
