import N6.Weighted49.GateGround000
import N6.Weighted49.FullColumnLayouts
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step000_vector : ∀ i : Fin 49, step000Left * vec_M001 i = step000Right * matVec matrix_B vec_M000 i := by
  intro i
  exact array_gate step000Left step000Right vec_M000Data vec_M001Data matrix_BColumns FullLists.B FullLists_B_layout rfl step000_list i
#print axioms step000_vector
theorem step001_vector : ∀ i : Fin 49, step001Left * vec_M002 i = step001Right * matVec matrix_c vec_M000 i := by
  intro i
  exact array_gate step001Left step001Right vec_M000Data vec_M002Data matrix_cColumns FullLists.c FullLists_c_layout rfl step001_list i
#print axioms step001_vector
theorem step002_vector : ∀ i : Fin 49, step002Left * vec_M003 i = step002Right * matVec matrix_e vec_M000 i := by
  intro i
  exact array_gate step002Left step002Right vec_M000Data vec_M003Data matrix_eColumns FullLists.e FullLists_e_layout rfl step002_list i
#print axioms step002_vector
theorem step003_vector : ∀ i : Fin 49, step003Left * vec_M004 i = step003Right * matVec matrix_B vec_M001 i := by
  intro i
  exact array_gate step003Left step003Right vec_M001Data vec_M004Data matrix_BColumns FullLists.B FullLists_B_layout rfl step003_list i
#print axioms step003_vector
theorem step004_vector : ∀ i : Fin 49, step004Left * vec_M005 i = step004Right * matVec matrix_c vec_M001 i := by
  intro i
  exact array_gate step004Left step004Right vec_M001Data vec_M005Data matrix_cColumns FullLists.c FullLists_c_layout rfl step004_list i
#print axioms step004_vector
theorem step005_vector : ∀ i : Fin 49, step005Left * vec_M006 i = step005Right * matVec matrix_c vec_M002 i := by
  intro i
  exact array_gate step005Left step005Right vec_M002Data vec_M006Data matrix_cColumns FullLists.c FullLists_c_layout rfl step005_list i
#print axioms step005_vector
theorem step006_vector : ∀ i : Fin 49, step006Left * vec_M007 i = step006Right * matVec matrix_k vec_M001 i := by
  intro i
  exact array_gate step006Left step006Right vec_M001Data vec_M007Data matrix_kColumns FullLists.k FullLists_k_layout rfl step006_list i
#print axioms step006_vector
theorem step007_vector : ∀ i : Fin 49, step007Left * vec_M008 i = step007Right * matVec matrix_e vec_M001 i := by
  intro i
  exact array_gate step007Left step007Right vec_M001Data vec_M008Data matrix_eColumns FullLists.e FullLists_e_layout rfl step007_list i
#print axioms step007_vector
theorem step008_vector : ∀ i : Fin 49, step008Left * vec_M009 i = step008Right * matVec matrix_e vec_M002 i := by
  intro i
  exact array_gate step008Left step008Right vec_M002Data vec_M009Data matrix_eColumns FullLists.e FullLists_e_layout rfl step008_list i
#print axioms step008_vector
theorem step009_vector : ∀ i : Fin 49, step009Left * vec_M010 i = step009Right * matVec matrix_e vec_M003 i := by
  intro i
  exact array_gate step009Left step009Right vec_M003Data vec_M010Data matrix_eColumns FullLists.e FullLists_e_layout rfl step009_list i
#print axioms step009_vector
theorem step010_vector : ∀ i : Fin 49, step010Left * vec_M011 i = step010Right * matVec matrix_B vec_M004 i := by
  intro i
  exact array_gate step010Left step010Right vec_M004Data vec_M011Data matrix_BColumns FullLists.B FullLists_B_layout rfl step010_list i
#print axioms step010_vector
theorem step011_vector : ∀ i : Fin 49, step011Left * vec_M012 i = step011Right * matVec matrix_c vec_M004 i := by
  intro i
  exact array_gate step011Left step011Right vec_M004Data vec_M012Data matrix_cColumns FullLists.c FullLists_c_layout rfl step011_list i
#print axioms step011_vector
theorem step012_vector : ∀ i : Fin 49, step012Left * vec_M013 i = step012Right * matVec matrix_c vec_M005 i := by
  intro i
  exact array_gate step012Left step012Right vec_M005Data vec_M013Data matrix_cColumns FullLists.c FullLists_c_layout rfl step012_list i
#print axioms step012_vector
theorem step013_vector : ∀ i : Fin 49, step013Left * vec_M014 i = step013Right * matVec matrix_c vec_M006 i := by
  intro i
  exact array_gate step013Left step013Right vec_M006Data vec_M014Data matrix_cColumns FullLists.c FullLists_c_layout rfl step013_list i
#print axioms step013_vector
theorem step014_vector : ∀ i : Fin 49, step014Left * vec_M015 i = step014Right * matVec matrix_k vec_M004 i := by
  intro i
  exact array_gate step014Left step014Right vec_M004Data vec_M015Data matrix_kColumns FullLists.k FullLists_k_layout rfl step014_list i
#print axioms step014_vector
theorem step015_vector : ∀ i : Fin 49, step015Left * vec_M016 i = step015Right * matVec matrix_k vec_M005 i := by
  intro i
  exact array_gate step015Left step015Right vec_M005Data vec_M016Data matrix_kColumns FullLists.k FullLists_k_layout rfl step015_list i
#print axioms step015_vector
end N6.Weighted49
