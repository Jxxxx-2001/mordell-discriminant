import N6.Weighted49.VecData
import N6.Weighted49.FullColumnListsData
import N6.Weighted49.ColumnCore
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem step161_nonzero : step161Left ≠ 0 := by decide +kernel
theorem step161_scale : step161Left * den_K022 = step161Right * matrix_BDen * den_K021 := by decide +kernel
theorem step161_list : scaleList step161Left vec_K022Data.toList = scaleList step161Right (foldColumns 49 vec_K021Data.toList FullLists.B) := by decide +kernel
#print axioms step161_list
theorem step162_nonzero : step162Left ≠ 0 := by decide +kernel
theorem step162_scale : step162Left * den_K023 = step162Right * matrix_BDen * den_K022 := by decide +kernel
theorem step162_list : scaleList step162Left vec_K023Data.toList = scaleList step162Right (foldColumns 49 vec_K022Data.toList FullLists.B) := by decide +kernel
#print axioms step162_list
theorem step163_nonzero : step163Left ≠ 0 := by decide +kernel
theorem step163_scale : step163Left * den_K024 = step163Right * matrix_BDen * den_K023 := by decide +kernel
theorem step163_list : scaleList step163Left vec_K024Data.toList = scaleList step163Right (foldColumns 49 vec_K023Data.toList FullLists.B) := by decide +kernel
#print axioms step163_list
theorem step164_nonzero : step164Left ≠ 0 := by decide +kernel
theorem step164_scale : step164Left * den_K025 = step164Right * matrix_BDen * den_K024 := by decide +kernel
theorem step164_list : scaleList step164Left vec_K025Data.toList = scaleList step164Right (foldColumns 49 vec_K024Data.toList FullLists.B) := by decide +kernel
#print axioms step164_list
theorem step165_nonzero : step165Left ≠ 0 := by decide +kernel
theorem step165_scale : step165Left * den_K026 = step165Right * matrix_BDen * den_K025 := by decide +kernel
theorem step165_list : scaleList step165Left vec_K026Data.toList = scaleList step165Right (foldColumns 49 vec_K025Data.toList FullLists.B) := by decide +kernel
#print axioms step165_list
theorem step166_nonzero : step166Left ≠ 0 := by decide +kernel
theorem step166_scale : step166Left * den_K027 = step166Right * matrix_BDen * den_K026 := by decide +kernel
theorem step166_list : scaleList step166Left vec_K027Data.toList = scaleList step166Right (foldColumns 49 vec_K026Data.toList FullLists.B) := by decide +kernel
#print axioms step166_list
theorem step167_nonzero : step167Left ≠ 0 := by decide +kernel
theorem step167_scale : step167Left * den_K028 = step167Right * matrix_BDen * den_K027 := by decide +kernel
theorem step167_list : scaleList step167Left vec_K028Data.toList = scaleList step167Right (foldColumns 49 vec_K027Data.toList FullLists.B) := by decide +kernel
#print axioms step167_list
theorem step168_nonzero : step168Left ≠ 0 := by decide +kernel
theorem step168_scale : step168Left * den_K029 = step168Right * matrix_BDen * den_K028 := by decide +kernel
theorem step168_list : scaleList step168Left vec_K029Data.toList = scaleList step168Right (foldColumns 49 vec_K028Data.toList FullLists.B) := by decide +kernel
#print axioms step168_list
theorem step169_nonzero : step169Left ≠ 0 := by decide +kernel
theorem step169_scale : step169Left * den_K030 = step169Right * matrix_BDen * den_K029 := by decide +kernel
theorem step169_list : scaleList step169Left vec_K030Data.toList = scaleList step169Right (foldColumns 49 vec_K029Data.toList FullLists.B) := by decide +kernel
#print axioms step169_list
theorem step170_nonzero : step170Left ≠ 0 := by decide +kernel
theorem step170_scale : step170Left * den_K031 = step170Right * matrix_BDen * den_K030 := by decide +kernel
theorem step170_list : scaleList step170Left vec_K031Data.toList = scaleList step170Right (foldColumns 49 vec_K030Data.toList FullLists.B) := by decide +kernel
#print axioms step170_list
theorem step171_nonzero : step171Left ≠ 0 := by decide +kernel
theorem step171_scale : step171Left * den_K032 = step171Right * matrix_BDen * den_K031 := by decide +kernel
theorem step171_list : scaleList step171Left vec_K032Data.toList = scaleList step171Right (foldColumns 49 vec_K031Data.toList FullLists.B) := by decide +kernel
#print axioms step171_list
theorem step172_nonzero : step172Left ≠ 0 := by decide +kernel
theorem step172_scale : step172Left * den_K033 = step172Right * matrix_BDen * den_K032 := by decide +kernel
theorem step172_list : scaleList step172Left vec_K033Data.toList = scaleList step172Right (foldColumns 49 vec_K032Data.toList FullLists.B) := by decide +kernel
#print axioms step172_list
theorem step173_nonzero : step173Left ≠ 0 := by decide +kernel
theorem step173_scale : step173Left * den_K034 = step173Right * matrix_BDen * den_K033 := by decide +kernel
theorem step173_list : scaleList step173Left vec_K034Data.toList = scaleList step173Right (foldColumns 49 vec_K033Data.toList FullLists.B) := by decide +kernel
#print axioms step173_list
theorem step174_nonzero : step174Left ≠ 0 := by decide +kernel
theorem step174_scale : step174Left * den_K035 = step174Right * matrix_BDen * den_K034 := by decide +kernel
theorem step174_list : scaleList step174Left vec_K035Data.toList = scaleList step174Right (foldColumns 49 vec_K034Data.toList FullLists.B) := by decide +kernel
#print axioms step174_list
end N6.Weighted49
