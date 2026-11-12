import N6.Weighted49.GateGround009
import N6.Weighted49.FullColumnLayouts
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step145_vector : ∀ i : Fin 49, step145Left * vec_K006 i = step145Right * matVec matrix_B vec_K005 i := by
  intro i
  exact array_gate step145Left step145Right vec_K005Data vec_K006Data matrix_BColumns FullLists.B FullLists_B_layout rfl step145_list i
#print axioms step145_vector
theorem step146_vector : ∀ i : Fin 49, step146Left * vec_K007 i = step146Right * matVec matrix_B vec_K006 i := by
  intro i
  exact array_gate step146Left step146Right vec_K006Data vec_K007Data matrix_BColumns FullLists.B FullLists_B_layout rfl step146_list i
#print axioms step146_vector
theorem step147_vector : ∀ i : Fin 49, step147Left * vec_K008 i = step147Right * matVec matrix_B vec_K007 i := by
  intro i
  exact array_gate step147Left step147Right vec_K007Data vec_K008Data matrix_BColumns FullLists.B FullLists_B_layout rfl step147_list i
#print axioms step147_vector
theorem step148_vector : ∀ i : Fin 49, step148Left * vec_K009 i = step148Right * matVec matrix_B vec_K008 i := by
  intro i
  exact array_gate step148Left step148Right vec_K008Data vec_K009Data matrix_BColumns FullLists.B FullLists_B_layout rfl step148_list i
#print axioms step148_vector
theorem step149_vector : ∀ i : Fin 49, step149Left * vec_K010 i = step149Right * matVec matrix_B vec_K009 i := by
  intro i
  exact array_gate step149Left step149Right vec_K009Data vec_K010Data matrix_BColumns FullLists.B FullLists_B_layout rfl step149_list i
#print axioms step149_vector
theorem step150_vector : ∀ i : Fin 49, step150Left * vec_K011 i = step150Right * matVec matrix_B vec_K010 i := by
  intro i
  exact array_gate step150Left step150Right vec_K010Data vec_K011Data matrix_BColumns FullLists.B FullLists_B_layout rfl step150_list i
#print axioms step150_vector
theorem step151_vector : ∀ i : Fin 49, step151Left * vec_K012 i = step151Right * matVec matrix_B vec_K011 i := by
  intro i
  exact array_gate step151Left step151Right vec_K011Data vec_K012Data matrix_BColumns FullLists.B FullLists_B_layout rfl step151_list i
#print axioms step151_vector
theorem step152_vector : ∀ i : Fin 49, step152Left * vec_K013 i = step152Right * matVec matrix_B vec_K012 i := by
  intro i
  exact array_gate step152Left step152Right vec_K012Data vec_K013Data matrix_BColumns FullLists.B FullLists_B_layout rfl step152_list i
#print axioms step152_vector
theorem step153_vector : ∀ i : Fin 49, step153Left * vec_K014 i = step153Right * matVec matrix_B vec_K013 i := by
  intro i
  exact array_gate step153Left step153Right vec_K013Data vec_K014Data matrix_BColumns FullLists.B FullLists_B_layout rfl step153_list i
#print axioms step153_vector
theorem step154_vector : ∀ i : Fin 49, step154Left * vec_K015 i = step154Right * matVec matrix_B vec_K014 i := by
  intro i
  exact array_gate step154Left step154Right vec_K014Data vec_K015Data matrix_BColumns FullLists.B FullLists_B_layout rfl step154_list i
#print axioms step154_vector
theorem step155_vector : ∀ i : Fin 49, step155Left * vec_K016 i = step155Right * matVec matrix_B vec_K015 i := by
  intro i
  exact array_gate step155Left step155Right vec_K015Data vec_K016Data matrix_BColumns FullLists.B FullLists_B_layout rfl step155_list i
#print axioms step155_vector
theorem step156_vector : ∀ i : Fin 49, step156Left * vec_K017 i = step156Right * matVec matrix_B vec_K016 i := by
  intro i
  exact array_gate step156Left step156Right vec_K016Data vec_K017Data matrix_BColumns FullLists.B FullLists_B_layout rfl step156_list i
#print axioms step156_vector
theorem step157_vector : ∀ i : Fin 49, step157Left * vec_K018 i = step157Right * matVec matrix_B vec_K017 i := by
  intro i
  exact array_gate step157Left step157Right vec_K017Data vec_K018Data matrix_BColumns FullLists.B FullLists_B_layout rfl step157_list i
#print axioms step157_vector
theorem step158_vector : ∀ i : Fin 49, step158Left * vec_K019 i = step158Right * matVec matrix_B vec_K018 i := by
  intro i
  exact array_gate step158Left step158Right vec_K018Data vec_K019Data matrix_BColumns FullLists.B FullLists_B_layout rfl step158_list i
#print axioms step158_vector
theorem step159_vector : ∀ i : Fin 49, step159Left * vec_K020 i = step159Right * matVec matrix_B vec_K019 i := by
  intro i
  exact array_gate step159Left step159Right vec_K019Data vec_K020Data matrix_BColumns FullLists.B FullLists_B_layout rfl step159_list i
#print axioms step159_vector
theorem step160_vector : ∀ i : Fin 49, step160Left * vec_K021 i = step160Right * matVec matrix_B vec_K020 i := by
  intro i
  exact array_gate step160Left step160Right vec_K020Data vec_K021Data matrix_BColumns FullLists.B FullLists_B_layout rfl step160_list i
#print axioms step160_vector
end N6.Weighted49
