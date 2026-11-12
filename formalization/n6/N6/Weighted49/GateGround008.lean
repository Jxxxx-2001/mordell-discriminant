import N6.Weighted49.VecData
import N6.Weighted49.FullColumnListsData
import N6.Weighted49.ColumnCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step128_nonzero : step128Left ≠ 0 := by decide +kernel
theorem step128_scale : step128Left * den_M129 = step128Right * matrix_eDen * den_M102 := by decide +kernel
theorem step128_list : scaleList step128Left vec_M129Data.toList = scaleList step128Right (foldColumns 49 vec_M102Data.toList FullLists.e) := by decide +kernel
theorem step128_monomial : mon_M129 = mon_M102.plus (variableMon 1) := by decide +kernel
#print axioms step128_list
theorem step129_nonzero : step129Left ≠ 0 := by decide +kernel
theorem step129_scale : step129Left * den_M130 = step129Right * matrix_kDen * den_M112 := by decide +kernel
theorem step129_list : scaleList step129Left vec_M130Data.toList = scaleList step129Right (foldColumns 49 vec_M112Data.toList FullLists.k) := by decide +kernel
theorem step129_monomial : mon_M130 = mon_M112.plus (variableMon 2) := by decide +kernel
#print axioms step129_list
theorem step130_nonzero : step130Left ≠ 0 := by decide +kernel
theorem step130_scale : step130Left * den_M131 = step130Right * matrix_kDen * den_M114 := by decide +kernel
theorem step130_list : scaleList step130Left vec_M131Data.toList = scaleList step130Right (foldColumns 49 vec_M114Data.toList FullLists.k) := by decide +kernel
theorem step130_monomial : mon_M131 = mon_M114.plus (variableMon 2) := by decide +kernel
#print axioms step130_list
theorem step131_nonzero : step131Left ≠ 0 := by decide +kernel
theorem step131_scale : step131Left * den_M132 = step131Right * matrix_kDen * den_M117 := by decide +kernel
theorem step131_list : scaleList step131Left vec_M132Data.toList = scaleList step131Right (foldColumns 49 vec_M117Data.toList FullLists.k) := by decide +kernel
theorem step131_monomial : mon_M132 = mon_M117.plus (variableMon 2) := by decide +kernel
#print axioms step131_list
theorem step132_nonzero : step132Left ≠ 0 := by decide +kernel
theorem step132_scale : step132Left * den_M133 = step132Right * matrix_kDen * den_M118 := by decide +kernel
theorem step132_list : scaleList step132Left vec_M133Data.toList = scaleList step132Right (foldColumns 49 vec_M118Data.toList FullLists.k) := by decide +kernel
theorem step132_monomial : mon_M133 = mon_M118.plus (variableMon 2) := by decide +kernel
#print axioms step132_list
theorem step133_nonzero : step133Left ≠ 0 := by decide +kernel
theorem step133_scale : step133Left * den_M134 = step133Right * matrix_kDen * den_M119 := by decide +kernel
theorem step133_list : scaleList step133Left vec_M134Data.toList = scaleList step133Right (foldColumns 49 vec_M119Data.toList FullLists.k) := by decide +kernel
theorem step133_monomial : mon_M134 = mon_M119.plus (variableMon 2) := by decide +kernel
#print axioms step133_list
theorem step134_nonzero : step134Left ≠ 0 := by decide +kernel
theorem step134_scale : step134Left * den_M135 = step134Right * matrix_eDen * den_M120 := by decide +kernel
theorem step134_list : scaleList step134Left vec_M135Data.toList = scaleList step134Right (foldColumns 49 vec_M120Data.toList FullLists.e) := by decide +kernel
theorem step134_monomial : mon_M135 = mon_M120.plus (variableMon 1) := by decide +kernel
#print axioms step134_list
theorem step135_nonzero : step135Left ≠ 0 := by decide +kernel
theorem step135_scale : step135Left * den_M136 = step135Right * matrix_kDen * den_M134 := by decide +kernel
theorem step135_list : scaleList step135Left vec_M136Data.toList = scaleList step135Right (foldColumns 49 vec_M134Data.toList FullLists.k) := by decide +kernel
theorem step135_monomial : mon_M136 = mon_M134.plus (variableMon 2) := by decide +kernel
#print axioms step135_list
theorem step137_nonzero : step137Left ≠ 0 := by decide +kernel
theorem step137_scale : step137Left * den_D_c = step137Right * matrix_cDen * den_K000 := by decide +kernel
theorem step137_list : scaleList step137Left vec_D_cData.toList = scaleList step137Right (foldColumns 49 vec_K000Data.toList FullLists.c) := by decide +kernel
#print axioms step137_list
theorem step138_nonzero : step138Left ≠ 0 := by decide +kernel
theorem step138_scale : step138Left * den_D_k = step138Right * matrix_kDen * den_K000 := by decide +kernel
theorem step138_list : scaleList step138Left vec_D_kData.toList = scaleList step138Right (foldColumns 49 vec_K000Data.toList FullLists.k) := by decide +kernel
#print axioms step138_list
theorem step139_nonzero : step139Left ≠ 0 := by decide +kernel
theorem step139_scale : step139Left * den_D_e = step139Right * matrix_eDen * den_K000 := by decide +kernel
theorem step139_list : scaleList step139Left vec_D_eData.toList = scaleList step139Right (foldColumns 49 vec_K000Data.toList FullLists.e) := by decide +kernel
#print axioms step139_list
theorem step140_nonzero : step140Left ≠ 0 := by decide +kernel
theorem step140_scale : step140Left * den_K001 = step140Right * matrix_BDen * den_K000 := by decide +kernel
theorem step140_list : scaleList step140Left vec_K001Data.toList = scaleList step140Right (foldColumns 49 vec_K000Data.toList FullLists.B) := by decide +kernel
#print axioms step140_list
theorem step141_nonzero : step141Left ≠ 0 := by decide +kernel
theorem step141_scale : step141Left * den_K002 = step141Right * matrix_BDen * den_K001 := by decide +kernel
theorem step141_list : scaleList step141Left vec_K002Data.toList = scaleList step141Right (foldColumns 49 vec_K001Data.toList FullLists.B) := by decide +kernel
#print axioms step141_list
theorem step142_nonzero : step142Left ≠ 0 := by decide +kernel
theorem step142_scale : step142Left * den_K003 = step142Right * matrix_BDen * den_K002 := by decide +kernel
theorem step142_list : scaleList step142Left vec_K003Data.toList = scaleList step142Right (foldColumns 49 vec_K002Data.toList FullLists.B) := by decide +kernel
#print axioms step142_list
theorem step143_nonzero : step143Left ≠ 0 := by decide +kernel
theorem step143_scale : step143Left * den_K004 = step143Right * matrix_BDen * den_K003 := by decide +kernel
theorem step143_list : scaleList step143Left vec_K004Data.toList = scaleList step143Right (foldColumns 49 vec_K003Data.toList FullLists.B) := by decide +kernel
#print axioms step143_list
theorem step144_nonzero : step144Left ≠ 0 := by decide +kernel
theorem step144_scale : step144Left * den_K005 = step144Right * matrix_BDen * den_K004 := by decide +kernel
theorem step144_list : scaleList step144Left vec_K005Data.toList = scaleList step144Right (foldColumns 49 vec_K004Data.toList FullLists.B) := by decide +kernel
#print axioms step144_list
end N6.Weighted49
