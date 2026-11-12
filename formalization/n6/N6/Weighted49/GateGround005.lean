import N6.Weighted49.VecData
import N6.Weighted49.FullColumnListsData
import N6.Weighted49.ColumnCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step080_nonzero : step080Left ≠ 0 := by decide +kernel
theorem step080_scale : step080Left * den_M081 = step080Right * matrix_cDen * den_M051 := by decide +kernel
theorem step080_list : scaleList step080Left vec_M081Data.toList = scaleList step080Right (foldColumns 49 vec_M051Data.toList FullLists.c) := by decide +kernel
theorem step080_monomial : mon_M081 = mon_M051.plus (variableMon 3) := by decide +kernel
#print axioms step080_list
theorem step081_nonzero : step081Left ≠ 0 := by decide +kernel
theorem step081_scale : step081Left * den_M082 = step081Right * matrix_cDen * den_M052 := by decide +kernel
theorem step081_list : scaleList step081Left vec_M082Data.toList = scaleList step081Right (foldColumns 49 vec_M052Data.toList FullLists.c) := by decide +kernel
theorem step081_monomial : mon_M082 = mon_M052.plus (variableMon 3) := by decide +kernel
#print axioms step081_list
theorem step082_nonzero : step082Left ≠ 0 := by decide +kernel
theorem step082_scale : step082Left * den_M083 = step082Right * matrix_kDen * den_M049 := by decide +kernel
theorem step082_list : scaleList step082Left vec_M083Data.toList = scaleList step082Right (foldColumns 49 vec_M049Data.toList FullLists.k) := by decide +kernel
theorem step082_monomial : mon_M083 = mon_M049.plus (variableMon 2) := by decide +kernel
#print axioms step082_list
theorem step083_nonzero : step083Left ≠ 0 := by decide +kernel
theorem step083_scale : step083Left * den_M084 = step083Right * matrix_kDen * den_M050 := by decide +kernel
theorem step083_list : scaleList step083Left vec_M084Data.toList = scaleList step083Right (foldColumns 49 vec_M050Data.toList FullLists.k) := by decide +kernel
theorem step083_monomial : mon_M084 = mon_M050.plus (variableMon 2) := by decide +kernel
#print axioms step083_list
theorem step084_nonzero : step084Left ≠ 0 := by decide +kernel
theorem step084_scale : step084Left * den_M085 = step084Right * matrix_kDen * den_M051 := by decide +kernel
theorem step084_list : scaleList step084Left vec_M085Data.toList = scaleList step084Right (foldColumns 49 vec_M051Data.toList FullLists.k) := by decide +kernel
theorem step084_monomial : mon_M085 = mon_M051.plus (variableMon 2) := by decide +kernel
#print axioms step084_list
theorem step085_nonzero : step085Left ≠ 0 := by decide +kernel
theorem step085_scale : step085Left * den_M086 = step085Right * matrix_kDen * den_M053 := by decide +kernel
theorem step085_list : scaleList step085Left vec_M086Data.toList = scaleList step085Right (foldColumns 49 vec_M053Data.toList FullLists.k) := by decide +kernel
theorem step085_monomial : mon_M086 = mon_M053.plus (variableMon 2) := by decide +kernel
#print axioms step085_list
theorem step086_nonzero : step086Left ≠ 0 := by decide +kernel
theorem step086_scale : step086Left * den_M087 = step086Right * matrix_kDen * den_M054 := by decide +kernel
theorem step086_list : scaleList step086Left vec_M087Data.toList = scaleList step086Right (foldColumns 49 vec_M054Data.toList FullLists.k) := by decide +kernel
theorem step086_monomial : mon_M087 = mon_M054.plus (variableMon 2) := by decide +kernel
#print axioms step086_list
theorem step087_nonzero : step087Left ≠ 0 := by decide +kernel
theorem step087_scale : step087Left * den_M088 = step087Right * matrix_kDen * den_M055 := by decide +kernel
theorem step087_list : scaleList step087Left vec_M088Data.toList = scaleList step087Right (foldColumns 49 vec_M055Data.toList FullLists.k) := by decide +kernel
theorem step087_monomial : mon_M088 = mon_M055.plus (variableMon 2) := by decide +kernel
#print axioms step087_list
theorem step088_nonzero : step088Left ≠ 0 := by decide +kernel
theorem step088_scale : step088Left * den_M089 = step088Right * matrix_kDen * den_M056 := by decide +kernel
theorem step088_list : scaleList step088Left vec_M089Data.toList = scaleList step088Right (foldColumns 49 vec_M056Data.toList FullLists.k) := by decide +kernel
theorem step088_monomial : mon_M089 = mon_M056.plus (variableMon 2) := by decide +kernel
#print axioms step088_list
theorem step089_nonzero : step089Left ≠ 0 := by decide +kernel
theorem step089_scale : step089Left * den_M090 = step089Right * matrix_kDen * den_M057 := by decide +kernel
theorem step089_list : scaleList step089Left vec_M090Data.toList = scaleList step089Right (foldColumns 49 vec_M057Data.toList FullLists.k) := by decide +kernel
theorem step089_monomial : mon_M090 = mon_M057.plus (variableMon 2) := by decide +kernel
#print axioms step089_list
theorem step090_nonzero : step090Left ≠ 0 := by decide +kernel
theorem step090_scale : step090Left * den_M091 = step090Right * matrix_kDen * den_M058 := by decide +kernel
theorem step090_list : scaleList step090Left vec_M091Data.toList = scaleList step090Right (foldColumns 49 vec_M058Data.toList FullLists.k) := by decide +kernel
theorem step090_monomial : mon_M091 = mon_M058.plus (variableMon 2) := by decide +kernel
#print axioms step090_list
theorem step091_nonzero : step091Left ≠ 0 := by decide +kernel
theorem step091_scale : step091Left * den_M092 = step091Right * matrix_kDen * den_M060 := by decide +kernel
theorem step091_list : scaleList step091Left vec_M092Data.toList = scaleList step091Right (foldColumns 49 vec_M060Data.toList FullLists.k) := by decide +kernel
theorem step091_monomial : mon_M092 = mon_M060.plus (variableMon 2) := by decide +kernel
#print axioms step091_list
theorem step092_nonzero : step092Left ≠ 0 := by decide +kernel
theorem step092_scale : step092Left * den_M093 = step092Right * matrix_eDen * den_M050 := by decide +kernel
theorem step092_list : scaleList step092Left vec_M093Data.toList = scaleList step092Right (foldColumns 49 vec_M050Data.toList FullLists.e) := by decide +kernel
theorem step092_monomial : mon_M093 = mon_M050.plus (variableMon 1) := by decide +kernel
#print axioms step092_list
theorem step093_nonzero : step093Left ≠ 0 := by decide +kernel
theorem step093_scale : step093Left * den_M094 = step093Right * matrix_eDen * den_M051 := by decide +kernel
theorem step093_list : scaleList step093Left vec_M094Data.toList = scaleList step093Right (foldColumns 49 vec_M051Data.toList FullLists.e) := by decide +kernel
theorem step093_monomial : mon_M094 = mon_M051.plus (variableMon 1) := by decide +kernel
#print axioms step093_list
theorem step094_nonzero : step094Left ≠ 0 := by decide +kernel
theorem step094_scale : step094Left * den_M095 = step094Right * matrix_eDen * den_M052 := by decide +kernel
theorem step094_list : scaleList step094Left vec_M095Data.toList = scaleList step094Right (foldColumns 49 vec_M052Data.toList FullLists.e) := by decide +kernel
theorem step094_monomial : mon_M095 = mon_M052.plus (variableMon 1) := by decide +kernel
#print axioms step094_list
theorem step095_nonzero : step095Left ≠ 0 := by decide +kernel
theorem step095_scale : step095Left * den_M096 = step095Right * matrix_eDen * den_M054 := by decide +kernel
theorem step095_list : scaleList step095Left vec_M096Data.toList = scaleList step095Right (foldColumns 49 vec_M054Data.toList FullLists.e) := by decide +kernel
theorem step095_monomial : mon_M096 = mon_M054.plus (variableMon 1) := by decide +kernel
#print axioms step095_list
end N6.Weighted49
