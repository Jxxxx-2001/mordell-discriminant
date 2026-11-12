import N6.Weighted49.GateGround010
import N6.Weighted49.FullColumnLayouts
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step161_vector : ∀ i : Fin 49, step161Left * vec_K022 i = step161Right * matVec matrix_B vec_K021 i := by
  intro i
  exact array_gate step161Left step161Right vec_K021Data vec_K022Data matrix_BColumns FullLists.B FullLists_B_layout rfl step161_list i
#print axioms step161_vector
theorem step162_vector : ∀ i : Fin 49, step162Left * vec_K023 i = step162Right * matVec matrix_B vec_K022 i := by
  intro i
  exact array_gate step162Left step162Right vec_K022Data vec_K023Data matrix_BColumns FullLists.B FullLists_B_layout rfl step162_list i
#print axioms step162_vector
theorem step163_vector : ∀ i : Fin 49, step163Left * vec_K024 i = step163Right * matVec matrix_B vec_K023 i := by
  intro i
  exact array_gate step163Left step163Right vec_K023Data vec_K024Data matrix_BColumns FullLists.B FullLists_B_layout rfl step163_list i
#print axioms step163_vector
theorem step164_vector : ∀ i : Fin 49, step164Left * vec_K025 i = step164Right * matVec matrix_B vec_K024 i := by
  intro i
  exact array_gate step164Left step164Right vec_K024Data vec_K025Data matrix_BColumns FullLists.B FullLists_B_layout rfl step164_list i
#print axioms step164_vector
theorem step165_vector : ∀ i : Fin 49, step165Left * vec_K026 i = step165Right * matVec matrix_B vec_K025 i := by
  intro i
  exact array_gate step165Left step165Right vec_K025Data vec_K026Data matrix_BColumns FullLists.B FullLists_B_layout rfl step165_list i
#print axioms step165_vector
theorem step166_vector : ∀ i : Fin 49, step166Left * vec_K027 i = step166Right * matVec matrix_B vec_K026 i := by
  intro i
  exact array_gate step166Left step166Right vec_K026Data vec_K027Data matrix_BColumns FullLists.B FullLists_B_layout rfl step166_list i
#print axioms step166_vector
theorem step167_vector : ∀ i : Fin 49, step167Left * vec_K028 i = step167Right * matVec matrix_B vec_K027 i := by
  intro i
  exact array_gate step167Left step167Right vec_K027Data vec_K028Data matrix_BColumns FullLists.B FullLists_B_layout rfl step167_list i
#print axioms step167_vector
theorem step168_vector : ∀ i : Fin 49, step168Left * vec_K029 i = step168Right * matVec matrix_B vec_K028 i := by
  intro i
  exact array_gate step168Left step168Right vec_K028Data vec_K029Data matrix_BColumns FullLists.B FullLists_B_layout rfl step168_list i
#print axioms step168_vector
theorem step169_vector : ∀ i : Fin 49, step169Left * vec_K030 i = step169Right * matVec matrix_B vec_K029 i := by
  intro i
  exact array_gate step169Left step169Right vec_K029Data vec_K030Data matrix_BColumns FullLists.B FullLists_B_layout rfl step169_list i
#print axioms step169_vector
theorem step170_vector : ∀ i : Fin 49, step170Left * vec_K031 i = step170Right * matVec matrix_B vec_K030 i := by
  intro i
  exact array_gate step170Left step170Right vec_K030Data vec_K031Data matrix_BColumns FullLists.B FullLists_B_layout rfl step170_list i
#print axioms step170_vector
theorem step171_vector : ∀ i : Fin 49, step171Left * vec_K032 i = step171Right * matVec matrix_B vec_K031 i := by
  intro i
  exact array_gate step171Left step171Right vec_K031Data vec_K032Data matrix_BColumns FullLists.B FullLists_B_layout rfl step171_list i
#print axioms step171_vector
theorem step172_vector : ∀ i : Fin 49, step172Left * vec_K033 i = step172Right * matVec matrix_B vec_K032 i := by
  intro i
  exact array_gate step172Left step172Right vec_K032Data vec_K033Data matrix_BColumns FullLists.B FullLists_B_layout rfl step172_list i
#print axioms step172_vector
theorem step173_vector : ∀ i : Fin 49, step173Left * vec_K034 i = step173Right * matVec matrix_B vec_K033 i := by
  intro i
  exact array_gate step173Left step173Right vec_K033Data vec_K034Data matrix_BColumns FullLists.B FullLists_B_layout rfl step173_list i
#print axioms step173_vector
theorem step174_vector : ∀ i : Fin 49, step174Left * vec_K035 i = step174Right * matVec matrix_B vec_K034 i := by
  intro i
  exact array_gate step174Left step174Right vec_K034Data vec_K035Data matrix_BColumns FullLists.B FullLists_B_layout rfl step174_list i
#print axioms step174_vector
end N6.Weighted49
