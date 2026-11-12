import N6.Weighted49.VecData
import N6.Weighted49.FullColumnListsData
import N6.Weighted49.ColumnCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step064_nonzero : step064Left ≠ 0 := by decide +kernel
theorem step064_scale : step064Left * den_M065 = step064Right * matrix_eDen * den_M033 := by decide +kernel
theorem step064_list : scaleList step064Left vec_M065Data.toList = scaleList step064Right (foldColumns 49 vec_M033Data.toList FullLists.e) := by decide +kernel
theorem step064_monomial : mon_M065 = mon_M033.plus (variableMon 1) := by decide +kernel
#print axioms step064_list
theorem step065_nonzero : step065Left ≠ 0 := by decide +kernel
theorem step065_scale : step065Left * den_M066 = step065Right * matrix_eDen * den_M034 := by decide +kernel
theorem step065_list : scaleList step065Left vec_M066Data.toList = scaleList step065Right (foldColumns 49 vec_M034Data.toList FullLists.e) := by decide +kernel
theorem step065_monomial : mon_M066 = mon_M034.plus (variableMon 1) := by decide +kernel
#print axioms step065_list
theorem step066_nonzero : step066Left ≠ 0 := by decide +kernel
theorem step066_scale : step066Left * den_M067 = step066Right * matrix_eDen * den_M035 := by decide +kernel
theorem step066_list : scaleList step066Left vec_M067Data.toList = scaleList step066Right (foldColumns 49 vec_M035Data.toList FullLists.e) := by decide +kernel
theorem step066_monomial : mon_M067 = mon_M035.plus (variableMon 1) := by decide +kernel
#print axioms step066_list
theorem step067_nonzero : step067Left ≠ 0 := by decide +kernel
theorem step067_scale : step067Left * den_M068 = step067Right * matrix_eDen * den_M036 := by decide +kernel
theorem step067_list : scaleList step067Left vec_M068Data.toList = scaleList step067Right (foldColumns 49 vec_M036Data.toList FullLists.e) := by decide +kernel
theorem step067_monomial : mon_M068 = mon_M036.plus (variableMon 1) := by decide +kernel
#print axioms step067_list
theorem step068_nonzero : step068Left ≠ 0 := by decide +kernel
theorem step068_scale : step068Left * den_M069 = step068Right * matrix_eDen * den_M037 := by decide +kernel
theorem step068_list : scaleList step068Left vec_M069Data.toList = scaleList step068Right (foldColumns 49 vec_M037Data.toList FullLists.e) := by decide +kernel
theorem step068_monomial : mon_M069 = mon_M037.plus (variableMon 1) := by decide +kernel
#print axioms step068_list
theorem step069_nonzero : step069Left ≠ 0 := by decide +kernel
theorem step069_scale : step069Left * den_M070 = step069Right * matrix_eDen * den_M038 := by decide +kernel
theorem step069_list : scaleList step069Left vec_M070Data.toList = scaleList step069Right (foldColumns 49 vec_M038Data.toList FullLists.e) := by decide +kernel
theorem step069_monomial : mon_M070 = mon_M038.plus (variableMon 1) := by decide +kernel
#print axioms step069_list
theorem step070_nonzero : step070Left ≠ 0 := by decide +kernel
theorem step070_scale : step070Left * den_M071 = step070Right * matrix_eDen * den_M039 := by decide +kernel
theorem step070_list : scaleList step070Left vec_M071Data.toList = scaleList step070Right (foldColumns 49 vec_M039Data.toList FullLists.e) := by decide +kernel
theorem step070_monomial : mon_M071 = mon_M039.plus (variableMon 1) := by decide +kernel
#print axioms step070_list
theorem step071_nonzero : step071Left ≠ 0 := by decide +kernel
theorem step071_scale : step071Left * den_M072 = step071Right * matrix_eDen * den_M040 := by decide +kernel
theorem step071_list : scaleList step071Left vec_M072Data.toList = scaleList step071Right (foldColumns 49 vec_M040Data.toList FullLists.e) := by decide +kernel
theorem step071_monomial : mon_M072 = mon_M040.plus (variableMon 1) := by decide +kernel
#print axioms step071_list
theorem step072_nonzero : step072Left ≠ 0 := by decide +kernel
theorem step072_scale : step072Left * den_M073 = step072Right * matrix_eDen * den_M041 := by decide +kernel
theorem step072_list : scaleList step072Left vec_M073Data.toList = scaleList step072Right (foldColumns 49 vec_M041Data.toList FullLists.e) := by decide +kernel
theorem step072_monomial : mon_M073 = mon_M041.plus (variableMon 1) := by decide +kernel
#print axioms step072_list
theorem step073_nonzero : step073Left ≠ 0 := by decide +kernel
theorem step073_scale : step073Left * den_M074 = step073Right * matrix_eDen * den_M042 := by decide +kernel
theorem step073_list : scaleList step073Left vec_M074Data.toList = scaleList step073Right (foldColumns 49 vec_M042Data.toList FullLists.e) := by decide +kernel
theorem step073_monomial : mon_M074 = mon_M042.plus (variableMon 1) := by decide +kernel
#print axioms step073_list
theorem step074_nonzero : step074Left ≠ 0 := by decide +kernel
theorem step074_scale : step074Left * den_M075 = step074Right * matrix_eDen * den_M043 := by decide +kernel
theorem step074_list : scaleList step074Left vec_M075Data.toList = scaleList step074Right (foldColumns 49 vec_M043Data.toList FullLists.e) := by decide +kernel
theorem step074_monomial : mon_M075 = mon_M043.plus (variableMon 1) := by decide +kernel
#print axioms step074_list
theorem step075_nonzero : step075Left ≠ 0 := by decide +kernel
theorem step075_scale : step075Left * den_M076 = step075Right * matrix_eDen * den_M044 := by decide +kernel
theorem step075_list : scaleList step075Left vec_M076Data.toList = scaleList step075Right (foldColumns 49 vec_M044Data.toList FullLists.e) := by decide +kernel
theorem step075_monomial : mon_M076 = mon_M044.plus (variableMon 1) := by decide +kernel
#print axioms step075_list
theorem step076_nonzero : step076Left ≠ 0 := by decide +kernel
theorem step076_scale : step076Left * den_M077 = step076Right * matrix_eDen * den_M045 := by decide +kernel
theorem step076_list : scaleList step076Left vec_M077Data.toList = scaleList step076Right (foldColumns 49 vec_M045Data.toList FullLists.e) := by decide +kernel
theorem step076_monomial : mon_M077 = mon_M045.plus (variableMon 1) := by decide +kernel
#print axioms step076_list
theorem step077_nonzero : step077Left ≠ 0 := by decide +kernel
theorem step077_scale : step077Left * den_M078 = step077Right * matrix_eDen * den_M046 := by decide +kernel
theorem step077_list : scaleList step077Left vec_M078Data.toList = scaleList step077Right (foldColumns 49 vec_M046Data.toList FullLists.e) := by decide +kernel
theorem step077_monomial : mon_M078 = mon_M046.plus (variableMon 1) := by decide +kernel
#print axioms step077_list
theorem step078_nonzero : step078Left ≠ 0 := by decide +kernel
theorem step078_scale : step078Left * den_M079 = step078Right * matrix_eDen * den_M047 := by decide +kernel
theorem step078_list : scaleList step078Left vec_M079Data.toList = scaleList step078Right (foldColumns 49 vec_M047Data.toList FullLists.e) := by decide +kernel
theorem step078_monomial : mon_M079 = mon_M047.plus (variableMon 1) := by decide +kernel
#print axioms step078_list
theorem step079_nonzero : step079Left ≠ 0 := by decide +kernel
theorem step079_scale : step079Left * den_M080 = step079Right * matrix_eDen * den_M048 := by decide +kernel
theorem step079_list : scaleList step079Left vec_M080Data.toList = scaleList step079Right (foldColumns 49 vec_M048Data.toList FullLists.e) := by decide +kernel
theorem step079_monomial : mon_M080 = mon_M048.plus (variableMon 1) := by decide +kernel
#print axioms step079_list
end N6.Weighted49
