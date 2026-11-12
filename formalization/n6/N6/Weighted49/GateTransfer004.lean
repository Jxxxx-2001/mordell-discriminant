import N6.Weighted49.GateGround004
import N6.Weighted49.FullColumnLayouts
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step064_vector : ∀ i : Fin 49, step064Left * vec_M065 i = step064Right * matVec matrix_e vec_M033 i := by
  intro i
  exact array_gate step064Left step064Right vec_M033Data vec_M065Data matrix_eColumns FullLists.e FullLists_e_layout rfl step064_list i
#print axioms step064_vector
theorem step065_vector : ∀ i : Fin 49, step065Left * vec_M066 i = step065Right * matVec matrix_e vec_M034 i := by
  intro i
  exact array_gate step065Left step065Right vec_M034Data vec_M066Data matrix_eColumns FullLists.e FullLists_e_layout rfl step065_list i
#print axioms step065_vector
theorem step066_vector : ∀ i : Fin 49, step066Left * vec_M067 i = step066Right * matVec matrix_e vec_M035 i := by
  intro i
  exact array_gate step066Left step066Right vec_M035Data vec_M067Data matrix_eColumns FullLists.e FullLists_e_layout rfl step066_list i
#print axioms step066_vector
theorem step067_vector : ∀ i : Fin 49, step067Left * vec_M068 i = step067Right * matVec matrix_e vec_M036 i := by
  intro i
  exact array_gate step067Left step067Right vec_M036Data vec_M068Data matrix_eColumns FullLists.e FullLists_e_layout rfl step067_list i
#print axioms step067_vector
theorem step068_vector : ∀ i : Fin 49, step068Left * vec_M069 i = step068Right * matVec matrix_e vec_M037 i := by
  intro i
  exact array_gate step068Left step068Right vec_M037Data vec_M069Data matrix_eColumns FullLists.e FullLists_e_layout rfl step068_list i
#print axioms step068_vector
theorem step069_vector : ∀ i : Fin 49, step069Left * vec_M070 i = step069Right * matVec matrix_e vec_M038 i := by
  intro i
  exact array_gate step069Left step069Right vec_M038Data vec_M070Data matrix_eColumns FullLists.e FullLists_e_layout rfl step069_list i
#print axioms step069_vector
theorem step070_vector : ∀ i : Fin 49, step070Left * vec_M071 i = step070Right * matVec matrix_e vec_M039 i := by
  intro i
  exact array_gate step070Left step070Right vec_M039Data vec_M071Data matrix_eColumns FullLists.e FullLists_e_layout rfl step070_list i
#print axioms step070_vector
theorem step071_vector : ∀ i : Fin 49, step071Left * vec_M072 i = step071Right * matVec matrix_e vec_M040 i := by
  intro i
  exact array_gate step071Left step071Right vec_M040Data vec_M072Data matrix_eColumns FullLists.e FullLists_e_layout rfl step071_list i
#print axioms step071_vector
theorem step072_vector : ∀ i : Fin 49, step072Left * vec_M073 i = step072Right * matVec matrix_e vec_M041 i := by
  intro i
  exact array_gate step072Left step072Right vec_M041Data vec_M073Data matrix_eColumns FullLists.e FullLists_e_layout rfl step072_list i
#print axioms step072_vector
theorem step073_vector : ∀ i : Fin 49, step073Left * vec_M074 i = step073Right * matVec matrix_e vec_M042 i := by
  intro i
  exact array_gate step073Left step073Right vec_M042Data vec_M074Data matrix_eColumns FullLists.e FullLists_e_layout rfl step073_list i
#print axioms step073_vector
theorem step074_vector : ∀ i : Fin 49, step074Left * vec_M075 i = step074Right * matVec matrix_e vec_M043 i := by
  intro i
  exact array_gate step074Left step074Right vec_M043Data vec_M075Data matrix_eColumns FullLists.e FullLists_e_layout rfl step074_list i
#print axioms step074_vector
theorem step075_vector : ∀ i : Fin 49, step075Left * vec_M076 i = step075Right * matVec matrix_e vec_M044 i := by
  intro i
  exact array_gate step075Left step075Right vec_M044Data vec_M076Data matrix_eColumns FullLists.e FullLists_e_layout rfl step075_list i
#print axioms step075_vector
theorem step076_vector : ∀ i : Fin 49, step076Left * vec_M077 i = step076Right * matVec matrix_e vec_M045 i := by
  intro i
  exact array_gate step076Left step076Right vec_M045Data vec_M077Data matrix_eColumns FullLists.e FullLists_e_layout rfl step076_list i
#print axioms step076_vector
theorem step077_vector : ∀ i : Fin 49, step077Left * vec_M078 i = step077Right * matVec matrix_e vec_M046 i := by
  intro i
  exact array_gate step077Left step077Right vec_M046Data vec_M078Data matrix_eColumns FullLists.e FullLists_e_layout rfl step077_list i
#print axioms step077_vector
theorem step078_vector : ∀ i : Fin 49, step078Left * vec_M079 i = step078Right * matVec matrix_e vec_M047 i := by
  intro i
  exact array_gate step078Left step078Right vec_M047Data vec_M079Data matrix_eColumns FullLists.e FullLists_e_layout rfl step078_list i
#print axioms step078_vector
theorem step079_vector : ∀ i : Fin 49, step079Left * vec_M080 i = step079Right * matVec matrix_e vec_M048 i := by
  intro i
  exact array_gate step079Left step079Right vec_M048Data vec_M080Data matrix_eColumns FullLists.e FullLists_e_layout rfl step079_list i
#print axioms step079_vector
end N6.Weighted49
