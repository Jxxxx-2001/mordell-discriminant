import N6.Weighted49.FullColumnListsData
import N6.Weighted49.ArithmeticFoldSemantics
set_option maxRecDepth 32000
set_option maxHeartbeats 3000000
set_option linter.unusedVariables false
namespace N6.Weighted49
open N6.SparseCheck N6.KroneckerCheck
theorem FullLists_e_layout : FullLists.e = matrix_eColumns.toList.map Array.toList := rfl
theorem FullLists_k_layout : FullLists.k = matrix_kColumns.toList.map Array.toList := rfl
theorem FullLists_c_layout : FullLists.c = matrix_cColumns.toList.map Array.toList := rfl
theorem FullLists_B_layout : FullLists.B = matrix_BColumns.toList.map Array.toList := rfl
end N6.Weighted49
