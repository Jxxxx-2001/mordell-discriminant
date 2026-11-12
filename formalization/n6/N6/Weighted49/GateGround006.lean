import N6.Weighted49.VecData
import N6.Weighted49.FullColumnListsData
import N6.Weighted49.ColumnCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step096_nonzero : step096Left ≠ 0 := by decide +kernel
theorem step096_scale : step096Left * den_M097 = step096Right * matrix_eDen * den_M055 := by decide +kernel
theorem step096_list : scaleList step096Left vec_M097Data.toList = scaleList step096Right (foldColumns 49 vec_M055Data.toList FullLists.e) := by decide +kernel
theorem step096_monomial : mon_M097 = mon_M055.plus (variableMon 1) := by decide +kernel
#print axioms step096_list
theorem step097_nonzero : step097Left ≠ 0 := by decide +kernel
theorem step097_scale : step097Left * den_M098 = step097Right * matrix_eDen * den_M056 := by decide +kernel
theorem step097_list : scaleList step097Left vec_M098Data.toList = scaleList step097Right (foldColumns 49 vec_M056Data.toList FullLists.e) := by decide +kernel
theorem step097_monomial : mon_M098 = mon_M056.plus (variableMon 1) := by decide +kernel
#print axioms step097_list
theorem step098_nonzero : step098Left ≠ 0 := by decide +kernel
theorem step098_scale : step098Left * den_M099 = step098Right * matrix_eDen * den_M057 := by decide +kernel
theorem step098_list : scaleList step098Left vec_M099Data.toList = scaleList step098Right (foldColumns 49 vec_M057Data.toList FullLists.e) := by decide +kernel
theorem step098_monomial : mon_M099 = mon_M057.plus (variableMon 1) := by decide +kernel
#print axioms step098_list
theorem step099_nonzero : step099Left ≠ 0 := by decide +kernel
theorem step099_scale : step099Left * den_M100 = step099Right * matrix_eDen * den_M058 := by decide +kernel
theorem step099_list : scaleList step099Left vec_M100Data.toList = scaleList step099Right (foldColumns 49 vec_M058Data.toList FullLists.e) := by decide +kernel
theorem step099_monomial : mon_M100 = mon_M058.plus (variableMon 1) := by decide +kernel
#print axioms step099_list
theorem step100_nonzero : step100Left ≠ 0 := by decide +kernel
theorem step100_scale : step100Left * den_M101 = step100Right * matrix_eDen * den_M059 := by decide +kernel
theorem step100_list : scaleList step100Left vec_M101Data.toList = scaleList step100Right (foldColumns 49 vec_M059Data.toList FullLists.e) := by decide +kernel
theorem step100_monomial : mon_M101 = mon_M059.plus (variableMon 1) := by decide +kernel
#print axioms step100_list
theorem step101_nonzero : step101Left ≠ 0 := by decide +kernel
theorem step101_scale : step101Left * den_M102 = step101Right * matrix_eDen * den_M060 := by decide +kernel
theorem step101_list : scaleList step101Left vec_M102Data.toList = scaleList step101Right (foldColumns 49 vec_M060Data.toList FullLists.e) := by decide +kernel
theorem step101_monomial : mon_M102 = mon_M060.plus (variableMon 1) := by decide +kernel
#print axioms step101_list
theorem step102_nonzero : step102Left ≠ 0 := by decide +kernel
theorem step102_scale : step102Left * den_M103 = step102Right * matrix_eDen * den_M061 := by decide +kernel
theorem step102_list : scaleList step102Left vec_M103Data.toList = scaleList step102Right (foldColumns 49 vec_M061Data.toList FullLists.e) := by decide +kernel
theorem step102_monomial : mon_M103 = mon_M061.plus (variableMon 1) := by decide +kernel
#print axioms step102_list
theorem step103_nonzero : step103Left ≠ 0 := by decide +kernel
theorem step103_scale : step103Left * den_M104 = step103Right * matrix_eDen * den_M062 := by decide +kernel
theorem step103_list : scaleList step103Left vec_M104Data.toList = scaleList step103Right (foldColumns 49 vec_M062Data.toList FullLists.e) := by decide +kernel
theorem step103_monomial : mon_M104 = mon_M062.plus (variableMon 1) := by decide +kernel
#print axioms step103_list
theorem step104_nonzero : step104Left ≠ 0 := by decide +kernel
theorem step104_scale : step104Left * den_M105 = step104Right * matrix_eDen * den_M063 := by decide +kernel
theorem step104_list : scaleList step104Left vec_M105Data.toList = scaleList step104Right (foldColumns 49 vec_M063Data.toList FullLists.e) := by decide +kernel
theorem step104_monomial : mon_M105 = mon_M063.plus (variableMon 1) := by decide +kernel
#print axioms step104_list
theorem step105_nonzero : step105Left ≠ 0 := by decide +kernel
theorem step105_scale : step105Left * den_M106 = step105Right * matrix_eDen * den_M064 := by decide +kernel
theorem step105_list : scaleList step105Left vec_M106Data.toList = scaleList step105Right (foldColumns 49 vec_M064Data.toList FullLists.e) := by decide +kernel
theorem step105_monomial : mon_M106 = mon_M064.plus (variableMon 1) := by decide +kernel
#print axioms step105_list
theorem step106_nonzero : step106Left ≠ 0 := by decide +kernel
theorem step106_scale : step106Left * den_M107 = step106Right * matrix_eDen * den_M065 := by decide +kernel
theorem step106_list : scaleList step106Left vec_M107Data.toList = scaleList step106Right (foldColumns 49 vec_M065Data.toList FullLists.e) := by decide +kernel
theorem step106_monomial : mon_M107 = mon_M065.plus (variableMon 1) := by decide +kernel
#print axioms step106_list
theorem step107_nonzero : step107Left ≠ 0 := by decide +kernel
theorem step107_scale : step107Left * den_M108 = step107Right * matrix_eDen * den_M066 := by decide +kernel
theorem step107_list : scaleList step107Left vec_M108Data.toList = scaleList step107Right (foldColumns 49 vec_M066Data.toList FullLists.e) := by decide +kernel
theorem step107_monomial : mon_M108 = mon_M066.plus (variableMon 1) := by decide +kernel
#print axioms step107_list
theorem step108_nonzero : step108Left ≠ 0 := by decide +kernel
theorem step108_scale : step108Left * den_M109 = step108Right * matrix_eDen * den_M070 := by decide +kernel
theorem step108_list : scaleList step108Left vec_M109Data.toList = scaleList step108Right (foldColumns 49 vec_M070Data.toList FullLists.e) := by decide +kernel
theorem step108_monomial : mon_M109 = mon_M070.plus (variableMon 1) := by decide +kernel
#print axioms step108_list
theorem step109_nonzero : step109Left ≠ 0 := by decide +kernel
theorem step109_scale : step109Left * den_M110 = step109Right * matrix_eDen * den_M072 := by decide +kernel
theorem step109_list : scaleList step109Left vec_M110Data.toList = scaleList step109Right (foldColumns 49 vec_M072Data.toList FullLists.e) := by decide +kernel
theorem step109_monomial : mon_M110 = mon_M072.plus (variableMon 1) := by decide +kernel
#print axioms step109_list
theorem step110_nonzero : step110Left ≠ 0 := by decide +kernel
theorem step110_scale : step110Left * den_M111 = step110Right * matrix_eDen * den_M073 := by decide +kernel
theorem step110_list : scaleList step110Left vec_M111Data.toList = scaleList step110Right (foldColumns 49 vec_M073Data.toList FullLists.e) := by decide +kernel
theorem step110_monomial : mon_M111 = mon_M073.plus (variableMon 1) := by decide +kernel
#print axioms step110_list
theorem step111_nonzero : step111Left ≠ 0 := by decide +kernel
theorem step111_scale : step111Left * den_M112 = step111Right * matrix_kDen * den_M081 := by decide +kernel
theorem step111_list : scaleList step111Left vec_M112Data.toList = scaleList step111Right (foldColumns 49 vec_M081Data.toList FullLists.k) := by decide +kernel
theorem step111_monomial : mon_M112 = mon_M081.plus (variableMon 2) := by decide +kernel
#print axioms step111_list
end N6.Weighted49
