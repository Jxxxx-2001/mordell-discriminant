import N6.Weighted49.VecData
import N6.Weighted49.FullColumnListsData
import N6.Weighted49.ColumnCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step112_nonzero : step112Left ≠ 0 := by decide +kernel
theorem step112_scale : step112Left * den_M113 = step112Right * matrix_kDen * den_M083 := by decide +kernel
theorem step112_list : scaleList step112Left vec_M113Data.toList = scaleList step112Right (foldColumns 49 vec_M083Data.toList FullLists.k) := by decide +kernel
theorem step112_monomial : mon_M113 = mon_M083.plus (variableMon 2) := by decide +kernel
#print axioms step112_list
theorem step113_nonzero : step113Left ≠ 0 := by decide +kernel
theorem step113_scale : step113Left * den_M114 = step113Right * matrix_kDen * den_M084 := by decide +kernel
theorem step113_list : scaleList step113Left vec_M114Data.toList = scaleList step113Right (foldColumns 49 vec_M084Data.toList FullLists.k) := by decide +kernel
theorem step113_monomial : mon_M114 = mon_M084.plus (variableMon 2) := by decide +kernel
#print axioms step113_list
theorem step114_nonzero : step114Left ≠ 0 := by decide +kernel
theorem step114_scale : step114Left * den_M115 = step114Right * matrix_kDen * den_M085 := by decide +kernel
theorem step114_list : scaleList step114Left vec_M115Data.toList = scaleList step114Right (foldColumns 49 vec_M085Data.toList FullLists.k) := by decide +kernel
theorem step114_monomial : mon_M115 = mon_M085.plus (variableMon 2) := by decide +kernel
#print axioms step114_list
theorem step115_nonzero : step115Left ≠ 0 := by decide +kernel
theorem step115_scale : step115Left * den_M116 = step115Right * matrix_kDen * den_M086 := by decide +kernel
theorem step115_list : scaleList step115Left vec_M116Data.toList = scaleList step115Right (foldColumns 49 vec_M086Data.toList FullLists.k) := by decide +kernel
theorem step115_monomial : mon_M116 = mon_M086.plus (variableMon 2) := by decide +kernel
#print axioms step115_list
theorem step116_nonzero : step116Left ≠ 0 := by decide +kernel
theorem step116_scale : step116Left * den_M117 = step116Right * matrix_kDen * den_M087 := by decide +kernel
theorem step116_list : scaleList step116Left vec_M117Data.toList = scaleList step116Right (foldColumns 49 vec_M087Data.toList FullLists.k) := by decide +kernel
theorem step116_monomial : mon_M117 = mon_M087.plus (variableMon 2) := by decide +kernel
#print axioms step116_list
theorem step117_nonzero : step117Left ≠ 0 := by decide +kernel
theorem step117_scale : step117Left * den_M118 = step117Right * matrix_kDen * den_M088 := by decide +kernel
theorem step117_list : scaleList step117Left vec_M118Data.toList = scaleList step117Right (foldColumns 49 vec_M088Data.toList FullLists.k) := by decide +kernel
theorem step117_monomial : mon_M118 = mon_M088.plus (variableMon 2) := by decide +kernel
#print axioms step117_list
theorem step118_nonzero : step118Left ≠ 0 := by decide +kernel
theorem step118_scale : step118Left * den_M119 = step118Right * matrix_kDen * den_M090 := by decide +kernel
theorem step118_list : scaleList step118Left vec_M119Data.toList = scaleList step118Right (foldColumns 49 vec_M090Data.toList FullLists.k) := by decide +kernel
theorem step118_monomial : mon_M119 = mon_M090.plus (variableMon 2) := by decide +kernel
#print axioms step118_list
theorem step119_nonzero : step119Left ≠ 0 := by decide +kernel
theorem step119_scale : step119Left * den_M120 = step119Right * matrix_kDen * den_M091 := by decide +kernel
theorem step119_list : scaleList step119Left vec_M120Data.toList = scaleList step119Right (foldColumns 49 vec_M091Data.toList FullLists.k) := by decide +kernel
theorem step119_monomial : mon_M120 = mon_M091.plus (variableMon 2) := by decide +kernel
#print axioms step119_list
theorem step120_nonzero : step120Left ≠ 0 := by decide +kernel
theorem step120_scale : step120Left * den_M121 = step120Right * matrix_eDen * den_M082 := by decide +kernel
theorem step120_list : scaleList step120Left vec_M121Data.toList = scaleList step120Right (foldColumns 49 vec_M082Data.toList FullLists.e) := by decide +kernel
theorem step120_monomial : mon_M121 = mon_M082.plus (variableMon 1) := by decide +kernel
#print axioms step120_list
theorem step121_nonzero : step121Left ≠ 0 := by decide +kernel
theorem step121_scale : step121Left * den_M122 = step121Right * matrix_eDen * den_M085 := by decide +kernel
theorem step121_list : scaleList step121Left vec_M122Data.toList = scaleList step121Right (foldColumns 49 vec_M085Data.toList FullLists.e) := by decide +kernel
theorem step121_monomial : mon_M122 = mon_M085.plus (variableMon 1) := by decide +kernel
#print axioms step121_list
theorem step122_nonzero : step122Left ≠ 0 := by decide +kernel
theorem step122_scale : step122Left * den_M123 = step122Right * matrix_eDen * den_M088 := by decide +kernel
theorem step122_list : scaleList step122Left vec_M123Data.toList = scaleList step122Right (foldColumns 49 vec_M088Data.toList FullLists.e) := by decide +kernel
theorem step122_monomial : mon_M123 = mon_M088.plus (variableMon 1) := by decide +kernel
#print axioms step122_list
theorem step123_nonzero : step123Left ≠ 0 := by decide +kernel
theorem step123_scale : step123Left * den_M124 = step123Right * matrix_eDen * den_M089 := by decide +kernel
theorem step123_list : scaleList step123Left vec_M124Data.toList = scaleList step123Right (foldColumns 49 vec_M089Data.toList FullLists.e) := by decide +kernel
theorem step123_monomial : mon_M124 = mon_M089.plus (variableMon 1) := by decide +kernel
#print axioms step123_list
theorem step124_nonzero : step124Left ≠ 0 := by decide +kernel
theorem step124_scale : step124Left * den_M125 = step124Right * matrix_eDen * den_M090 := by decide +kernel
theorem step124_list : scaleList step124Left vec_M125Data.toList = scaleList step124Right (foldColumns 49 vec_M090Data.toList FullLists.e) := by decide +kernel
theorem step124_monomial : mon_M125 = mon_M090.plus (variableMon 1) := by decide +kernel
#print axioms step124_list
theorem step125_nonzero : step125Left ≠ 0 := by decide +kernel
theorem step125_scale : step125Left * den_M126 = step125Right * matrix_eDen * den_M091 := by decide +kernel
theorem step125_list : scaleList step125Left vec_M126Data.toList = scaleList step125Right (foldColumns 49 vec_M091Data.toList FullLists.e) := by decide +kernel
theorem step125_monomial : mon_M126 = mon_M091.plus (variableMon 1) := by decide +kernel
#print axioms step125_list
theorem step126_nonzero : step126Left ≠ 0 := by decide +kernel
theorem step126_scale : step126Left * den_M127 = step126Right * matrix_eDen * den_M092 := by decide +kernel
theorem step126_list : scaleList step126Left vec_M127Data.toList = scaleList step126Right (foldColumns 49 vec_M092Data.toList FullLists.e) := by decide +kernel
theorem step126_monomial : mon_M127 = mon_M092.plus (variableMon 1) := by decide +kernel
#print axioms step126_list
theorem step127_nonzero : step127Left ≠ 0 := by decide +kernel
theorem step127_scale : step127Left * den_M128 = step127Right * matrix_eDen * den_M101 := by decide +kernel
theorem step127_list : scaleList step127Left vec_M128Data.toList = scaleList step127Right (foldColumns 49 vec_M101Data.toList FullLists.e) := by decide +kernel
theorem step127_monomial : mon_M128 = mon_M101.plus (variableMon 1) := by decide +kernel
#print axioms step127_list
end N6.Weighted49
