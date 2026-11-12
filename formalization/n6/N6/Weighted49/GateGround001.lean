import N6.Weighted49.VecData
import N6.Weighted49.FullColumnListsData
import N6.Weighted49.ColumnCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step016_nonzero : step016Left ≠ 0 := by decide +kernel
theorem step016_scale : step016Left * den_M017 = step016Right * matrix_kDen * den_M007 := by decide +kernel
theorem step016_list : scaleList step016Left vec_M017Data.toList = scaleList step016Right (foldColumns 49 vec_M007Data.toList FullLists.k) := by decide +kernel
theorem step016_monomial : mon_M017 = mon_M007.plus (variableMon 2) := by decide +kernel
#print axioms step016_list
theorem step017_nonzero : step017Left ≠ 0 := by decide +kernel
theorem step017_scale : step017Left * den_M018 = step017Right * matrix_eDen * den_M004 := by decide +kernel
theorem step017_list : scaleList step017Left vec_M018Data.toList = scaleList step017Right (foldColumns 49 vec_M004Data.toList FullLists.e) := by decide +kernel
theorem step017_monomial : mon_M018 = mon_M004.plus (variableMon 1) := by decide +kernel
#print axioms step017_list
theorem step018_nonzero : step018Left ≠ 0 := by decide +kernel
theorem step018_scale : step018Left * den_M019 = step018Right * matrix_eDen * den_M005 := by decide +kernel
theorem step018_list : scaleList step018Left vec_M019Data.toList = scaleList step018Right (foldColumns 49 vec_M005Data.toList FullLists.e) := by decide +kernel
theorem step018_monomial : mon_M019 = mon_M005.plus (variableMon 1) := by decide +kernel
#print axioms step018_list
theorem step019_nonzero : step019Left ≠ 0 := by decide +kernel
theorem step019_scale : step019Left * den_M020 = step019Right * matrix_eDen * den_M006 := by decide +kernel
theorem step019_list : scaleList step019Left vec_M020Data.toList = scaleList step019Right (foldColumns 49 vec_M006Data.toList FullLists.e) := by decide +kernel
theorem step019_monomial : mon_M020 = mon_M006.plus (variableMon 1) := by decide +kernel
#print axioms step019_list
theorem step020_nonzero : step020Left ≠ 0 := by decide +kernel
theorem step020_scale : step020Left * den_M021 = step020Right * matrix_eDen * den_M007 := by decide +kernel
theorem step020_list : scaleList step020Left vec_M021Data.toList = scaleList step020Right (foldColumns 49 vec_M007Data.toList FullLists.e) := by decide +kernel
theorem step020_monomial : mon_M021 = mon_M007.plus (variableMon 1) := by decide +kernel
#print axioms step020_list
theorem step021_nonzero : step021Left ≠ 0 := by decide +kernel
theorem step021_scale : step021Left * den_M022 = step021Right * matrix_eDen * den_M008 := by decide +kernel
theorem step021_list : scaleList step021Left vec_M022Data.toList = scaleList step021Right (foldColumns 49 vec_M008Data.toList FullLists.e) := by decide +kernel
theorem step021_monomial : mon_M022 = mon_M008.plus (variableMon 1) := by decide +kernel
#print axioms step021_list
theorem step022_nonzero : step022Left ≠ 0 := by decide +kernel
theorem step022_scale : step022Left * den_M023 = step022Right * matrix_eDen * den_M009 := by decide +kernel
theorem step022_list : scaleList step022Left vec_M023Data.toList = scaleList step022Right (foldColumns 49 vec_M009Data.toList FullLists.e) := by decide +kernel
theorem step022_monomial : mon_M023 = mon_M009.plus (variableMon 1) := by decide +kernel
#print axioms step022_list
theorem step023_nonzero : step023Left ≠ 0 := by decide +kernel
theorem step023_scale : step023Left * den_M024 = step023Right * matrix_eDen * den_M010 := by decide +kernel
theorem step023_list : scaleList step023Left vec_M024Data.toList = scaleList step023Right (foldColumns 49 vec_M010Data.toList FullLists.e) := by decide +kernel
theorem step023_monomial : mon_M024 = mon_M010.plus (variableMon 1) := by decide +kernel
#print axioms step023_list
theorem step024_nonzero : step024Left ≠ 0 := by decide +kernel
theorem step024_scale : step024Left * den_M025 = step024Right * matrix_BDen * den_M011 := by decide +kernel
theorem step024_list : scaleList step024Left vec_M025Data.toList = scaleList step024Right (foldColumns 49 vec_M011Data.toList FullLists.B) := by decide +kernel
theorem step024_monomial : mon_M025 = mon_M011.plus (variableMon 4) := by decide +kernel
#print axioms step024_list
theorem step025_nonzero : step025Left ≠ 0 := by decide +kernel
theorem step025_scale : step025Left * den_M026 = step025Right * matrix_cDen * den_M011 := by decide +kernel
theorem step025_list : scaleList step025Left vec_M026Data.toList = scaleList step025Right (foldColumns 49 vec_M011Data.toList FullLists.c) := by decide +kernel
theorem step025_monomial : mon_M026 = mon_M011.plus (variableMon 3) := by decide +kernel
#print axioms step025_list
theorem step026_nonzero : step026Left ≠ 0 := by decide +kernel
theorem step026_scale : step026Left * den_M027 = step026Right * matrix_cDen * den_M012 := by decide +kernel
theorem step026_list : scaleList step026Left vec_M027Data.toList = scaleList step026Right (foldColumns 49 vec_M012Data.toList FullLists.c) := by decide +kernel
theorem step026_monomial : mon_M027 = mon_M012.plus (variableMon 3) := by decide +kernel
#print axioms step026_list
theorem step027_nonzero : step027Left ≠ 0 := by decide +kernel
theorem step027_scale : step027Left * den_M028 = step027Right * matrix_cDen * den_M013 := by decide +kernel
theorem step027_list : scaleList step027Left vec_M028Data.toList = scaleList step027Right (foldColumns 49 vec_M013Data.toList FullLists.c) := by decide +kernel
theorem step027_monomial : mon_M028 = mon_M013.plus (variableMon 3) := by decide +kernel
#print axioms step027_list
theorem step028_nonzero : step028Left ≠ 0 := by decide +kernel
theorem step028_scale : step028Left * den_M029 = step028Right * matrix_cDen * den_M014 := by decide +kernel
theorem step028_list : scaleList step028Left vec_M029Data.toList = scaleList step028Right (foldColumns 49 vec_M014Data.toList FullLists.c) := by decide +kernel
theorem step028_monomial : mon_M029 = mon_M014.plus (variableMon 3) := by decide +kernel
#print axioms step028_list
theorem step029_nonzero : step029Left ≠ 0 := by decide +kernel
theorem step029_scale : step029Left * den_M030 = step029Right * matrix_kDen * den_M011 := by decide +kernel
theorem step029_list : scaleList step029Left vec_M030Data.toList = scaleList step029Right (foldColumns 49 vec_M011Data.toList FullLists.k) := by decide +kernel
theorem step029_monomial : mon_M030 = mon_M011.plus (variableMon 2) := by decide +kernel
#print axioms step029_list
theorem step030_nonzero : step030Left ≠ 0 := by decide +kernel
theorem step030_scale : step030Left * den_M031 = step030Right * matrix_kDen * den_M012 := by decide +kernel
theorem step030_list : scaleList step030Left vec_M031Data.toList = scaleList step030Right (foldColumns 49 vec_M012Data.toList FullLists.k) := by decide +kernel
theorem step030_monomial : mon_M031 = mon_M012.plus (variableMon 2) := by decide +kernel
#print axioms step030_list
theorem step031_nonzero : step031Left ≠ 0 := by decide +kernel
theorem step031_scale : step031Left * den_M032 = step031Right * matrix_kDen * den_M013 := by decide +kernel
theorem step031_list : scaleList step031Left vec_M032Data.toList = scaleList step031Right (foldColumns 49 vec_M013Data.toList FullLists.k) := by decide +kernel
theorem step031_monomial : mon_M032 = mon_M013.plus (variableMon 2) := by decide +kernel
#print axioms step031_list
end N6.Weighted49
