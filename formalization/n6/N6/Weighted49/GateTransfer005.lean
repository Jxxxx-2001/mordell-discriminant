import N6.Weighted49.GateGround005
import N6.Weighted49.FullColumnLayouts
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step080_vector : ∀ i : Fin 49, step080Left * vec_M081 i = step080Right * matVec matrix_c vec_M051 i := by
  intro i
  exact array_gate step080Left step080Right vec_M051Data vec_M081Data matrix_cColumns FullLists.c FullLists_c_layout rfl step080_list i
#print axioms step080_vector
theorem step081_vector : ∀ i : Fin 49, step081Left * vec_M082 i = step081Right * matVec matrix_c vec_M052 i := by
  intro i
  exact array_gate step081Left step081Right vec_M052Data vec_M082Data matrix_cColumns FullLists.c FullLists_c_layout rfl step081_list i
#print axioms step081_vector
theorem step082_vector : ∀ i : Fin 49, step082Left * vec_M083 i = step082Right * matVec matrix_k vec_M049 i := by
  intro i
  exact array_gate step082Left step082Right vec_M049Data vec_M083Data matrix_kColumns FullLists.k FullLists_k_layout rfl step082_list i
#print axioms step082_vector
theorem step083_vector : ∀ i : Fin 49, step083Left * vec_M084 i = step083Right * matVec matrix_k vec_M050 i := by
  intro i
  exact array_gate step083Left step083Right vec_M050Data vec_M084Data matrix_kColumns FullLists.k FullLists_k_layout rfl step083_list i
#print axioms step083_vector
theorem step084_vector : ∀ i : Fin 49, step084Left * vec_M085 i = step084Right * matVec matrix_k vec_M051 i := by
  intro i
  exact array_gate step084Left step084Right vec_M051Data vec_M085Data matrix_kColumns FullLists.k FullLists_k_layout rfl step084_list i
#print axioms step084_vector
theorem step085_vector : ∀ i : Fin 49, step085Left * vec_M086 i = step085Right * matVec matrix_k vec_M053 i := by
  intro i
  exact array_gate step085Left step085Right vec_M053Data vec_M086Data matrix_kColumns FullLists.k FullLists_k_layout rfl step085_list i
#print axioms step085_vector
theorem step086_vector : ∀ i : Fin 49, step086Left * vec_M087 i = step086Right * matVec matrix_k vec_M054 i := by
  intro i
  exact array_gate step086Left step086Right vec_M054Data vec_M087Data matrix_kColumns FullLists.k FullLists_k_layout rfl step086_list i
#print axioms step086_vector
theorem step087_vector : ∀ i : Fin 49, step087Left * vec_M088 i = step087Right * matVec matrix_k vec_M055 i := by
  intro i
  exact array_gate step087Left step087Right vec_M055Data vec_M088Data matrix_kColumns FullLists.k FullLists_k_layout rfl step087_list i
#print axioms step087_vector
theorem step088_vector : ∀ i : Fin 49, step088Left * vec_M089 i = step088Right * matVec matrix_k vec_M056 i := by
  intro i
  exact array_gate step088Left step088Right vec_M056Data vec_M089Data matrix_kColumns FullLists.k FullLists_k_layout rfl step088_list i
#print axioms step088_vector
theorem step089_vector : ∀ i : Fin 49, step089Left * vec_M090 i = step089Right * matVec matrix_k vec_M057 i := by
  intro i
  exact array_gate step089Left step089Right vec_M057Data vec_M090Data matrix_kColumns FullLists.k FullLists_k_layout rfl step089_list i
#print axioms step089_vector
theorem step090_vector : ∀ i : Fin 49, step090Left * vec_M091 i = step090Right * matVec matrix_k vec_M058 i := by
  intro i
  exact array_gate step090Left step090Right vec_M058Data vec_M091Data matrix_kColumns FullLists.k FullLists_k_layout rfl step090_list i
#print axioms step090_vector
theorem step091_vector : ∀ i : Fin 49, step091Left * vec_M092 i = step091Right * matVec matrix_k vec_M060 i := by
  intro i
  exact array_gate step091Left step091Right vec_M060Data vec_M092Data matrix_kColumns FullLists.k FullLists_k_layout rfl step091_list i
#print axioms step091_vector
theorem step092_vector : ∀ i : Fin 49, step092Left * vec_M093 i = step092Right * matVec matrix_e vec_M050 i := by
  intro i
  exact array_gate step092Left step092Right vec_M050Data vec_M093Data matrix_eColumns FullLists.e FullLists_e_layout rfl step092_list i
#print axioms step092_vector
theorem step093_vector : ∀ i : Fin 49, step093Left * vec_M094 i = step093Right * matVec matrix_e vec_M051 i := by
  intro i
  exact array_gate step093Left step093Right vec_M051Data vec_M094Data matrix_eColumns FullLists.e FullLists_e_layout rfl step093_list i
#print axioms step093_vector
theorem step094_vector : ∀ i : Fin 49, step094Left * vec_M095 i = step094Right * matVec matrix_e vec_M052 i := by
  intro i
  exact array_gate step094Left step094Right vec_M052Data vec_M095Data matrix_eColumns FullLists.e FullLists_e_layout rfl step094_list i
#print axioms step094_vector
theorem step095_vector : ∀ i : Fin 49, step095Left * vec_M096 i = step095Right * matVec matrix_e vec_M054 i := by
  intro i
  exact array_gate step095Left step095Right vec_M054Data vec_M096Data matrix_eColumns FullLists.e FullLists_e_layout rfl step095_list i
#print axioms step095_vector
end N6.Weighted49
