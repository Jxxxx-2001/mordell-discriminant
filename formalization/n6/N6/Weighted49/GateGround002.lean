import N6.Weighted49.VecData
import N6.Weighted49.FullColumnListsData
import N6.Weighted49.ColumnCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step032_nonzero : step032Left ≠ 0 := by decide +kernel
theorem step032_scale : step032Left * den_M033 = step032Right * matrix_kDen * den_M015 := by decide +kernel
theorem step032_list : scaleList step032Left vec_M033Data.toList = scaleList step032Right (foldColumns 49 vec_M015Data.toList FullLists.k) := by decide +kernel
theorem step032_monomial : mon_M033 = mon_M015.plus (variableMon 2) := by decide +kernel
#print axioms step032_list
theorem step033_nonzero : step033Left ≠ 0 := by decide +kernel
theorem step033_scale : step033Left * den_M034 = step033Right * matrix_kDen * den_M016 := by decide +kernel
theorem step033_list : scaleList step033Left vec_M034Data.toList = scaleList step033Right (foldColumns 49 vec_M016Data.toList FullLists.k) := by decide +kernel
theorem step033_monomial : mon_M034 = mon_M016.plus (variableMon 2) := by decide +kernel
#print axioms step033_list
theorem step034_nonzero : step034Left ≠ 0 := by decide +kernel
theorem step034_scale : step034Left * den_M035 = step034Right * matrix_eDen * den_M011 := by decide +kernel
theorem step034_list : scaleList step034Left vec_M035Data.toList = scaleList step034Right (foldColumns 49 vec_M011Data.toList FullLists.e) := by decide +kernel
theorem step034_monomial : mon_M035 = mon_M011.plus (variableMon 1) := by decide +kernel
#print axioms step034_list
theorem step035_nonzero : step035Left ≠ 0 := by decide +kernel
theorem step035_scale : step035Left * den_M036 = step035Right * matrix_eDen * den_M012 := by decide +kernel
theorem step035_list : scaleList step035Left vec_M036Data.toList = scaleList step035Right (foldColumns 49 vec_M012Data.toList FullLists.e) := by decide +kernel
theorem step035_monomial : mon_M036 = mon_M012.plus (variableMon 1) := by decide +kernel
#print axioms step035_list
theorem step036_nonzero : step036Left ≠ 0 := by decide +kernel
theorem step036_scale : step036Left * den_M037 = step036Right * matrix_eDen * den_M013 := by decide +kernel
theorem step036_list : scaleList step036Left vec_M037Data.toList = scaleList step036Right (foldColumns 49 vec_M013Data.toList FullLists.e) := by decide +kernel
theorem step036_monomial : mon_M037 = mon_M013.plus (variableMon 1) := by decide +kernel
#print axioms step036_list
theorem step037_nonzero : step037Left ≠ 0 := by decide +kernel
theorem step037_scale : step037Left * den_M038 = step037Right * matrix_eDen * den_M014 := by decide +kernel
theorem step037_list : scaleList step037Left vec_M038Data.toList = scaleList step037Right (foldColumns 49 vec_M014Data.toList FullLists.e) := by decide +kernel
theorem step037_monomial : mon_M038 = mon_M014.plus (variableMon 1) := by decide +kernel
#print axioms step037_list
theorem step038_nonzero : step038Left ≠ 0 := by decide +kernel
theorem step038_scale : step038Left * den_M039 = step038Right * matrix_eDen * den_M015 := by decide +kernel
theorem step038_list : scaleList step038Left vec_M039Data.toList = scaleList step038Right (foldColumns 49 vec_M015Data.toList FullLists.e) := by decide +kernel
theorem step038_monomial : mon_M039 = mon_M015.plus (variableMon 1) := by decide +kernel
#print axioms step038_list
theorem step039_nonzero : step039Left ≠ 0 := by decide +kernel
theorem step039_scale : step039Left * den_M040 = step039Right * matrix_eDen * den_M016 := by decide +kernel
theorem step039_list : scaleList step039Left vec_M040Data.toList = scaleList step039Right (foldColumns 49 vec_M016Data.toList FullLists.e) := by decide +kernel
theorem step039_monomial : mon_M040 = mon_M016.plus (variableMon 1) := by decide +kernel
#print axioms step039_list
theorem step040_nonzero : step040Left ≠ 0 := by decide +kernel
theorem step040_scale : step040Left * den_M041 = step040Right * matrix_eDen * den_M017 := by decide +kernel
theorem step040_list : scaleList step040Left vec_M041Data.toList = scaleList step040Right (foldColumns 49 vec_M017Data.toList FullLists.e) := by decide +kernel
theorem step040_monomial : mon_M041 = mon_M017.plus (variableMon 1) := by decide +kernel
#print axioms step040_list
theorem step041_nonzero : step041Left ≠ 0 := by decide +kernel
theorem step041_scale : step041Left * den_M042 = step041Right * matrix_eDen * den_M018 := by decide +kernel
theorem step041_list : scaleList step041Left vec_M042Data.toList = scaleList step041Right (foldColumns 49 vec_M018Data.toList FullLists.e) := by decide +kernel
theorem step041_monomial : mon_M042 = mon_M018.plus (variableMon 1) := by decide +kernel
#print axioms step041_list
theorem step042_nonzero : step042Left ≠ 0 := by decide +kernel
theorem step042_scale : step042Left * den_M043 = step042Right * matrix_eDen * den_M019 := by decide +kernel
theorem step042_list : scaleList step042Left vec_M043Data.toList = scaleList step042Right (foldColumns 49 vec_M019Data.toList FullLists.e) := by decide +kernel
theorem step042_monomial : mon_M043 = mon_M019.plus (variableMon 1) := by decide +kernel
#print axioms step042_list
theorem step043_nonzero : step043Left ≠ 0 := by decide +kernel
theorem step043_scale : step043Left * den_M044 = step043Right * matrix_eDen * den_M020 := by decide +kernel
theorem step043_list : scaleList step043Left vec_M044Data.toList = scaleList step043Right (foldColumns 49 vec_M020Data.toList FullLists.e) := by decide +kernel
theorem step043_monomial : mon_M044 = mon_M020.plus (variableMon 1) := by decide +kernel
#print axioms step043_list
theorem step044_nonzero : step044Left ≠ 0 := by decide +kernel
theorem step044_scale : step044Left * den_M045 = step044Right * matrix_eDen * den_M021 := by decide +kernel
theorem step044_list : scaleList step044Left vec_M045Data.toList = scaleList step044Right (foldColumns 49 vec_M021Data.toList FullLists.e) := by decide +kernel
theorem step044_monomial : mon_M045 = mon_M021.plus (variableMon 1) := by decide +kernel
#print axioms step044_list
theorem step045_nonzero : step045Left ≠ 0 := by decide +kernel
theorem step045_scale : step045Left * den_M046 = step045Right * matrix_eDen * den_M022 := by decide +kernel
theorem step045_list : scaleList step045Left vec_M046Data.toList = scaleList step045Right (foldColumns 49 vec_M022Data.toList FullLists.e) := by decide +kernel
theorem step045_monomial : mon_M046 = mon_M022.plus (variableMon 1) := by decide +kernel
#print axioms step045_list
theorem step046_nonzero : step046Left ≠ 0 := by decide +kernel
theorem step046_scale : step046Left * den_M047 = step046Right * matrix_eDen * den_M023 := by decide +kernel
theorem step046_list : scaleList step046Left vec_M047Data.toList = scaleList step046Right (foldColumns 49 vec_M023Data.toList FullLists.e) := by decide +kernel
theorem step046_monomial : mon_M047 = mon_M023.plus (variableMon 1) := by decide +kernel
#print axioms step046_list
theorem step047_nonzero : step047Left ≠ 0 := by decide +kernel
theorem step047_scale : step047Left * den_M048 = step047Right * matrix_eDen * den_M024 := by decide +kernel
theorem step047_list : scaleList step047Left vec_M048Data.toList = scaleList step047Right (foldColumns 49 vec_M024Data.toList FullLists.e) := by decide +kernel
theorem step047_monomial : mon_M048 = mon_M024.plus (variableMon 1) := by decide +kernel
#print axioms step047_list
end N6.Weighted49
