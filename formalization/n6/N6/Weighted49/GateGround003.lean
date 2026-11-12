import N6.Weighted49.VecData
import N6.Weighted49.FullColumnListsData
import N6.Weighted49.ColumnCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step048_nonzero : step048Left ≠ 0 := by decide +kernel
theorem step048_scale : step048Left * den_M049 = step048Right * matrix_cDen * den_M026 := by decide +kernel
theorem step048_list : scaleList step048Left vec_M049Data.toList = scaleList step048Right (foldColumns 49 vec_M026Data.toList FullLists.c) := by decide +kernel
theorem step048_monomial : mon_M049 = mon_M026.plus (variableMon 3) := by decide +kernel
#print axioms step048_list
theorem step049_nonzero : step049Left ≠ 0 := by decide +kernel
theorem step049_scale : step049Left * den_M050 = step049Right * matrix_cDen * den_M027 := by decide +kernel
theorem step049_list : scaleList step049Left vec_M050Data.toList = scaleList step049Right (foldColumns 49 vec_M027Data.toList FullLists.c) := by decide +kernel
theorem step049_monomial : mon_M050 = mon_M027.plus (variableMon 3) := by decide +kernel
#print axioms step049_list
theorem step050_nonzero : step050Left ≠ 0 := by decide +kernel
theorem step050_scale : step050Left * den_M051 = step050Right * matrix_cDen * den_M028 := by decide +kernel
theorem step050_list : scaleList step050Left vec_M051Data.toList = scaleList step050Right (foldColumns 49 vec_M028Data.toList FullLists.c) := by decide +kernel
theorem step050_monomial : mon_M051 = mon_M028.plus (variableMon 3) := by decide +kernel
#print axioms step050_list
theorem step051_nonzero : step051Left ≠ 0 := by decide +kernel
theorem step051_scale : step051Left * den_M052 = step051Right * matrix_cDen * den_M029 := by decide +kernel
theorem step051_list : scaleList step051Left vec_M052Data.toList = scaleList step051Right (foldColumns 49 vec_M029Data.toList FullLists.c) := by decide +kernel
theorem step051_monomial : mon_M052 = mon_M029.plus (variableMon 3) := by decide +kernel
#print axioms step051_list
theorem step052_nonzero : step052Left ≠ 0 := by decide +kernel
theorem step052_scale : step052Left * den_M053 = step052Right * matrix_kDen * den_M025 := by decide +kernel
theorem step052_list : scaleList step052Left vec_M053Data.toList = scaleList step052Right (foldColumns 49 vec_M025Data.toList FullLists.k) := by decide +kernel
theorem step052_monomial : mon_M053 = mon_M025.plus (variableMon 2) := by decide +kernel
#print axioms step052_list
theorem step053_nonzero : step053Left ≠ 0 := by decide +kernel
theorem step053_scale : step053Left * den_M054 = step053Right * matrix_kDen * den_M026 := by decide +kernel
theorem step053_list : scaleList step053Left vec_M054Data.toList = scaleList step053Right (foldColumns 49 vec_M026Data.toList FullLists.k) := by decide +kernel
theorem step053_monomial : mon_M054 = mon_M026.plus (variableMon 2) := by decide +kernel
#print axioms step053_list
theorem step054_nonzero : step054Left ≠ 0 := by decide +kernel
theorem step054_scale : step054Left * den_M055 = step054Right * matrix_kDen * den_M027 := by decide +kernel
theorem step054_list : scaleList step054Left vec_M055Data.toList = scaleList step054Right (foldColumns 49 vec_M027Data.toList FullLists.k) := by decide +kernel
theorem step054_monomial : mon_M055 = mon_M027.plus (variableMon 2) := by decide +kernel
#print axioms step054_list
theorem step055_nonzero : step055Left ≠ 0 := by decide +kernel
theorem step055_scale : step055Left * den_M056 = step055Right * matrix_kDen * den_M028 := by decide +kernel
theorem step055_list : scaleList step055Left vec_M056Data.toList = scaleList step055Right (foldColumns 49 vec_M028Data.toList FullLists.k) := by decide +kernel
theorem step055_monomial : mon_M056 = mon_M028.plus (variableMon 2) := by decide +kernel
#print axioms step055_list
theorem step056_nonzero : step056Left ≠ 0 := by decide +kernel
theorem step056_scale : step056Left * den_M057 = step056Right * matrix_kDen * den_M030 := by decide +kernel
theorem step056_list : scaleList step056Left vec_M057Data.toList = scaleList step056Right (foldColumns 49 vec_M030Data.toList FullLists.k) := by decide +kernel
theorem step056_monomial : mon_M057 = mon_M030.plus (variableMon 2) := by decide +kernel
#print axioms step056_list
theorem step057_nonzero : step057Left ≠ 0 := by decide +kernel
theorem step057_scale : step057Left * den_M058 = step057Right * matrix_kDen * den_M031 := by decide +kernel
theorem step057_list : scaleList step057Left vec_M058Data.toList = scaleList step057Right (foldColumns 49 vec_M031Data.toList FullLists.k) := by decide +kernel
theorem step057_monomial : mon_M058 = mon_M031.plus (variableMon 2) := by decide +kernel
#print axioms step057_list
theorem step058_nonzero : step058Left ≠ 0 := by decide +kernel
theorem step058_scale : step058Left * den_M059 = step058Right * matrix_kDen * den_M032 := by decide +kernel
theorem step058_list : scaleList step058Left vec_M059Data.toList = scaleList step058Right (foldColumns 49 vec_M032Data.toList FullLists.k) := by decide +kernel
theorem step058_monomial : mon_M059 = mon_M032.plus (variableMon 2) := by decide +kernel
#print axioms step058_list
theorem step059_nonzero : step059Left ≠ 0 := by decide +kernel
theorem step059_scale : step059Left * den_M060 = step059Right * matrix_kDen * den_M033 := by decide +kernel
theorem step059_list : scaleList step059Left vec_M060Data.toList = scaleList step059Right (foldColumns 49 vec_M033Data.toList FullLists.k) := by decide +kernel
theorem step059_monomial : mon_M060 = mon_M033.plus (variableMon 2) := by decide +kernel
#print axioms step059_list
theorem step060_nonzero : step060Left ≠ 0 := by decide +kernel
theorem step060_scale : step060Left * den_M061 = step060Right * matrix_eDen * den_M028 := by decide +kernel
theorem step060_list : scaleList step060Left vec_M061Data.toList = scaleList step060Right (foldColumns 49 vec_M028Data.toList FullLists.e) := by decide +kernel
theorem step060_monomial : mon_M061 = mon_M028.plus (variableMon 1) := by decide +kernel
#print axioms step060_list
theorem step061_nonzero : step061Left ≠ 0 := by decide +kernel
theorem step061_scale : step061Left * den_M062 = step061Right * matrix_eDen * den_M029 := by decide +kernel
theorem step061_list : scaleList step061Left vec_M062Data.toList = scaleList step061Right (foldColumns 49 vec_M029Data.toList FullLists.e) := by decide +kernel
theorem step061_monomial : mon_M062 = mon_M029.plus (variableMon 1) := by decide +kernel
#print axioms step061_list
theorem step062_nonzero : step062Left ≠ 0 := by decide +kernel
theorem step062_scale : step062Left * den_M063 = step062Right * matrix_eDen * den_M031 := by decide +kernel
theorem step062_list : scaleList step062Left vec_M063Data.toList = scaleList step062Right (foldColumns 49 vec_M031Data.toList FullLists.e) := by decide +kernel
theorem step062_monomial : mon_M063 = mon_M031.plus (variableMon 1) := by decide +kernel
#print axioms step062_list
theorem step063_nonzero : step063Left ≠ 0 := by decide +kernel
theorem step063_scale : step063Left * den_M064 = step063Right * matrix_eDen * den_M032 := by decide +kernel
theorem step063_list : scaleList step063Left vec_M064Data.toList = scaleList step063Right (foldColumns 49 vec_M032Data.toList FullLists.e) := by decide +kernel
theorem step063_monomial : mon_M064 = mon_M032.plus (variableMon 1) := by decide +kernel
#print axioms step063_list
end N6.Weighted49
